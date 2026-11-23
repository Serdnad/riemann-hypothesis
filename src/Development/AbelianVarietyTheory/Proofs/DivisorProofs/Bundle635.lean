module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle588
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.LatAll
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle003

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem differentiable_det_of {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by
  have : (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ i, y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [Matrix.of_apply]
  rw [this]
  fun_prop

theorem differentiable_update_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {r : ℕ}
    (x : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => Function.update x τ y) := by
  intro y
  exact (hasFDerivAt_update x y).differentiableAt

end GlobalTheory

namespace GlobalTheory

theorem section_slice_eq_poly_div_det_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ],
      (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) →
      ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) →
      ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ,
        ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧
          ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 →
            P (Function.update x τ y) =
              MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  intro E _ _ _ r X _ hdom la N hN P hP x hx τ
  classical

  have hupd : ∀ y : Fin r → Fin r → ℂ,
      Function.update x τ y ∈ X.dom ↔ (Matrix.of y).det ≠ 0 := by
    intro y
    rw [hdom]
    have hx' := (hdom x).1 hx
    constructor
    · intro h
      have := h τ
      simpa [mat] using this
    · intro h σ
      by_cases hσ : σ = τ
      · subst hσ
        simpa [mat] using h
      · simpa [mat, Function.update_of_ne hσ] using hx' σ
  let a : Fin r → ℕ := fun i => (la τ i + N).toNat
  let h : Matrix (Fin r) (Fin r) ℂ → ℂ := fun y =>
    P (Function.update x τ (fun i j => y i j)) * y.det ^ N

  have hholo : ReciprocityTheory.MultiplicativeHeights.IsHoloGL h := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsHoloGL
    have h1 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => P (Function.update x τ y))
        {y | (Matrix.of y).det ≠ 0} :=
      hP.1.comp (differentiable_update_frame x τ).differentiableOn
        (fun y hy => (hupd y).2 hy)
    have h2 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det ^ N)
        {y | (Matrix.of y).det ≠ 0} :=
      (differentiable_det_of.pow N).differentiableOn
    exact h1.mul h2

  have htri : ReciprocityTheory.MultiplicativeHeights.IsTriEquivariant a h := by
    intro y b hy hb hbt
    let b' : Frame X.Ψ r := fun σ => if σ = τ then b else (1 : Matrix (Fin r) (Fin r) ℂ)
    have hbτ : b' τ = b := by exact if_pos rfl
    have hbσ : ∀ σ, σ ≠ τ → b' σ = (1 : Matrix (Fin r) (Fin r) ℂ) := fun σ hσ => by exact if_neg hσ
    have hb'B : b' ∈ Bor X.Ψ r := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbτ]; exact hb
        · rw [hbτ]; exact hbt hcd
      · refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbσ σ hσ]; change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0; simp
        · rw [hbσ σ hσ, Matrix.one_apply, if_neg (ne_of_lt hcd).symm]
    have hrm : rmul (Function.update x τ (fun i j => y i j)) b' =
        Function.update x τ (fun i j => (y * b) i j) := by
      funext σ
      by_cases hσ : σ = τ
      · subst hσ
        change (Matrix.of (Function.update x σ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x σ (fun i j => (y * b) i j) σ
        rw [hbτ, Function.update_self, Function.update_self]
        rfl
      · change (Matrix.of (Function.update x τ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x τ (fun i j => (y * b) i j) σ
        rw [hbσ σ hσ, Function.update_of_ne hσ, Function.update_of_ne hσ]
        exact Matrix.mul_one _
    have hbc : bchar la b' = ∏ i, b i i ^ la τ i := by
      unfold bchar
      rw [Finset.prod_eq_single τ]
      · rw [hbτ]
      · intro σ _ hσ
        rw [hbσ σ hσ]
        exact Finset.prod_eq_one fun i _ => by simp
      · intro h'; exact absurd (Finset.mem_univ τ) h'
    have hmem : Function.update x τ (fun i j => y i j) ∈ X.dom := (hupd _).2 hy
    have hP2 := hP.2.1 _ hmem b' hb'B
    rw [hrm, hbc] at hP2
    have hdb : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular hbt
    have hbii : ∀ i, b i i ≠ 0 := by
      intro i
      rw [hdb] at hb
      exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)
    have hchar : (∏ i, b i i ^ la τ i) * b.det ^ N = ReciprocityTheory.MultiplicativeHeights.triChar a b := by
      rw [hdb, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      unfold ReciprocityTheory.MultiplicativeHeights.triChar
      refine Finset.prod_congr rfl fun i _ => ?_
      have e : ((la τ i + N).toNat : ℤ) = la τ i + N := Int.toNat_of_nonneg (hN τ i)
      rw [← zpow_natCast (b i i) N, ← zpow_add₀ (hbii i), ← zpow_natCast, e]
    show P (Function.update x τ (fun i j => (y * b) i j)) * (y * b).det ^ N =
      ReciprocityTheory.MultiplicativeHeights.triChar a b * (P (Function.update x τ (fun i j => y i j)) * y.det ^ N)
    rw [hP2, Matrix.det_mul, mul_pow, ← hchar]
    ring
  obtain ⟨F, hF, hFe⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.bwPoly r a h hholo htri
  refine ⟨F, hF, fun y hy => ?_⟩
  have e := hFe (Matrix.of y) hy
  have e' : P (Function.update x τ y) * (Matrix.of y).det ^ N =
      MvPolynomial.eval (fun ij => y ij.1 ij.2) F := e
  rw [← e', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy), mul_one]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.ProdLin

theorem exists_linearisation_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  intro X L hL Ga Gb _ _ ρ₁ ρ₂ ρ hρ hcomm hρ₁ hρ₂ v₁ v₂ hv₁ hv₂ hc₁ hc₂ hc
  have hex : ∀ p : Ga × Gb, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val u r z J = val (LB.mulGen L _ _ _ _ (v₁ p.1) (LB.pullGen L _ _ (v₂ p.2) (ρ₁ p.1))) r z J := by
    intro p
    refine exists_gen hL ?_ _ (DVR.mulGen_isGen_of_isGen _ (hv₁ _) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hv₂ _) _))
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two, hρ p]
  choose u hu hval using hex
  refine ⟨u, hu, fun p q => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  refine corr_of_val hL fun y J hJ => ?_
  have e0 := hval (a * c, b * d) X (𝟙 X) y J hJ
  have e1 := hval (a, b) X (𝟙 X) y J hJ
  have e2 := hval (c, d) X (𝟙 X ≫ ρ (a, b)) y J hJ
  have f1 := val_corr hJ (hc₁ a c) (𝟙 X)
  have f2 := val_corr hJ (hc₂ b d) (ρ₁ (a * c))
  have g := val_corr hJ (hc c b) (ρ₁ a)
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e0
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at g
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁]
  rw [e0, e1, e2, f1, f2, ← hcomm c b, _root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (val (v₁ c) (ρ₁ a) y J), g]
  simp only [_root_.mul_assoc]
end GlobalTheory.ProdLin
end
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem det_eq_det_minor_of_unit_rows {K : Type} [CommRing K] {i d : ℕ} (r : Fin i → Fin d)
    (hr : Function.Injective r) (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ e, e ∉ Set.range r → ∀ c, M e c = if c = e then 1 else 0) :
    M.det = (M.submatrix r r).det := by
  classical
  let E : Fin i ⊕ {e // e ∉ Set.range r} ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun e => e ∈ Set.range r))
  have hEl : ∀ a, E (Sum.inl a) = r a := fun a => rfl
  have hEr : ∀ e, E (Sum.inr e) = e.1 := fun e => rfl
  rw [← Matrix.det_submatrix_equiv_self E M, ← Matrix.fromBlocks_toBlocks (M.submatrix E E)]
  have h21 : (M.submatrix E E).toBlocks₂₁ = 0 := by
    ext e b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, hEl, hEr]
    rw [hM e.1 e.2, if_neg]
    rintro h
    exact e.2 ⟨b, h⟩
  have h22 : (M.submatrix E E).toBlocks₂₂ = 1 := by
    ext e e'
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, hEr, Matrix.one_apply]
    rw [hM e.1 e.2]
    by_cases hee : e = e'
    · subst hee; simp
    · rw [if_neg (fun h => hee (Subtype.ext h).symm), if_neg hee]
  have h11 : (M.submatrix E E).toBlocks₁₁ = M.submatrix r r := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hEl]
  rw [h21, Matrix.det_fromBlocks_zero₂₁, h22, Matrix.det_one, mul_one, h11]

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_basis_adapted_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h →
    ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ),
    (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C,
    IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
    ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C),
      IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧
      (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧
      ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  intro C _ _ _ v p hp hv d h hh ty G hmu τ j i hj u hu hut
  classical
  obtain ⟨hPT2, -⟩ := GlobalTheory.T.typicalCurveEigenspace_and_basisExists
  choose η hηc hηt hηtan using fun a : Fin i =>
    hPT2 C v p hp hv d h hh ty G hmu τ (u a) (hu.1 a) (hut a)
  have hspan : Module.finrank C (Submodule.span C (Set.range fun a =>
      (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1))) ≤ j := by
    let W := Submodule.span C
      (Set.range fun e : {e : Fin d // ty e = τ + 1} => (Pi.single e.1 (1 : C) : Fin d → C))
    have hle : Submodule.span C (Set.range fun a =>
        (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1)) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      show G.lc p (η a) 1 ∈ W
      rw [← Finset.univ_sum_single (G.lc p (η a) 1)]
      refine Submodule.sum_mem _ fun e _ => ?_
      by_cases he : ty e = τ + 1
      · have : (Pi.single e (G.lc p (η a) 1 e) : Fin d → C) =
            G.lc p (η a) 1 e • (Pi.single e (1 : C) : Fin d → C) := by
          ext c; simp [Pi.single_apply]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e, he⟩, rfl⟩)
      · rw [(hηt a).2 1 e (by simpa using he), Pi.single_zero]
        exact Submodule.zero_mem _
    calc _ ≤ Module.finrank C W := Submodule.finrank_mono hle
      _ ≤ Fintype.card {e : Fin d // ty e = τ + 1} := finrank_range_le_card _
      _ = _ := Fintype.card_subtype _
      _ ≤ j := hj
  obtain ⟨x, hxi, hxd, hxt, hxty, hxl⟩ := GlobalTheory.T.root_extraction_lemma_sheaf C v p hp hv d h i ty τ G η
    (fun a => hηc a) (fun a => hηt a) 1 j le_rfl (Fin d → C) LinearMap.id hspan
  set γ' : Fin i → Fin d → PowerSeries C :=
    fun w => G.sumF fun u => rescaleCurve (x w u) (η u) with hγ'
  have hγ'c : ∀ w, IsCurve v (γ' w) := fun w =>
    (pt6' C v p hp hv d i G η (x w) (fun a => hηc a) (fun a => hxi w a)).1
  obtain ⟨r0, hr0⟩ := hu.2
  set U : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r0 b) with hU
  have hUne : U.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr0
    exact WithTop.top_ne_zero hr0
  have hinj : Function.Injective r0 := by
    intro b1 b2 heq
    by_contra hne
    exact hUne (Matrix.det_zero_of_column_eq hne (fun a => by simp [hU, heq]))
  have hty0 : ∀ b, ty (r0 b) = τ := by
    intro b
    by_contra hne
    exact hUne (Matrix.det_eq_zero_of_column_eq_zero b (fun a => by simp [hU, hut a _ hne]))
  choose ζ hζc hζt hζtan using fun e : Fin d =>
    hPT2 C v p hp hv d h hh ty G hmu (ty e) (Pi.single e 1)
      (fun c => by
        unfold IsIntV
        by_cases hc : c = e
        · subst hc; simp
        · simp [Pi.single_apply, hc])
      (fun c hc => by
        have : c ≠ e := fun h' => hc (h' ▸ rfl)
        simp [Pi.single_apply, this])
  let γ : Fin d → Fin d → PowerSeries C := fun e =>
    if hm : e ∈ Set.range r0 then γ' ((Equiv.ofInjective r0 hinj).symm ⟨e, hm⟩) else ζ e
  have hγr : ∀ a, γ (r0 a) = γ' a := by
    intro a
    simp only [γ, dif_pos (Set.mem_range_self a)]
    rw [Equiv.ofInjective_symm_apply]
  have hγn : ∀ e, e ∉ Set.range r0 → γ e = ζ e := fun e he => by simp only [γ, dif_neg he]
  have htan : ∀ a, tangent (γ (r0 a)) = ∑ a', x a a' • u a' := by
    intro a
    rw [hγr, hxt a]
    simp only [hηtan]
  refine ⟨γ, ⟨r0, hinj⟩, x, ⟨fun e => ?_, fun e => ?_, ?_⟩, hxi, hxd, htan, fun a ha => ?_⟩
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr]; exact hγ'c b
    · rw [hγn e he]; exact hζc e
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr, hty0]; exact hxty b
    · rw [hγn e he]; exact hζt e
  · rw [det_eq_det_minor_of_unit_rows r0 hinj]
    · have hsub : (Matrix.of fun a b => tangent (γ a) b).submatrix r0 r0 = x * U := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, htan, Matrix.mul_apply, hU,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsub, Matrix.det_mul, AddValuation.map_mul, hxd, hr0, add_zero]
    · intro e he c
      simp only [Matrix.of_apply, hγn e he, hζtan, Pi.single_apply]
  · show G.lc p (γ (r0 a)) 1 = 0
    rw [hγr]
    simpa using hxl a ha

end GlobalTheory.FGDepth
end
