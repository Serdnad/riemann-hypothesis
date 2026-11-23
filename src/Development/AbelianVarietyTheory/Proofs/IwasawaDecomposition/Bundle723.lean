module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle714
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle697
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle713
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsExpChart e ex → 0 < ρ → ρ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) → ∃ ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ), IsExpChart ch (fun x v => ex x (P (e x) *ᵥ v)) ∧ (∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ) ∧ ∀ x ∈ ch.source, e x = ρ • ch x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex P ρ hE hρ hρ1 hP hPu
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hE
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  let ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ) :=
    (e.restrOpen _ hSo).transHomeomorph (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0))
  have hch : ∀ x, ch x = (ρ⁻¹ : ℝ) • e x := fun x ↦ rfl
  have hchs : ∀ z, ch.symm z = e.symm (ρ • z) := fun z ↦ by
    show e.symm ((ρ⁻¹ : ℝ)⁻¹ • z) = _
    rw [inv_inv]
  have hsrc : ∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun x ↦ by
    show x ∈ e.source ∩ (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hball : ∀ z : Fin n → ℂ, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    intro z
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hsub : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ρ • z ∈ e.target := fun z hz ↦ by
    rw [htarget]; exact Metric.ball_subset_ball hρ1 ((hball z).2 hz)
  have htgt : ch.target = Metric.ball 0 1 := by
    ext z
    show (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z ∈
      e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    have hz : (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z = ρ • z := by
      show (ρ⁻¹ : ℝ)⁻¹ • z = _
      rw [inv_inv]
    rw [hz]
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, -, h⟩
      rw [e.right_inv h1] at h
      exact (hball z).1 h
    · intro h
      have h2 := hsub z h
      exact ⟨h2, e.map_target h2, by rw [e.right_inv h2]; exact (hball z).2 h⟩
  refine ⟨ch, ⟨htgt, ?_, ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · intro k V _ _ _ B x hB hx hm
    have := hholE k V B x hB hx fun b hb ↦ ((hsrc _).1 (hm hb)).1
    simp only [hch, Pi.smul_apply]
    exact this.const_smul (ρ⁻¹ : ℝ)
  · rw [htgt]
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun z : Fin n → ℂ ↦ ρ • z) hsymmHol Metric.isOpen_ball
      (differentiableOn_id.const_smul ρ) fun z hz ↦ hsub z hz
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun z _ ↦ ?_
    simp only [hchs]
  · intro x hx v w
    simp only [Matrix.mulVec_add]
    exact hadd x ((hsrc x).1 hx).1 _ _
  · rw [htgt]
    have hφ : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ (ρ • zw.1, P (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      refine (differentiableOn_fst.const_smul ρ).prodMk ?_
      refine differentiableOn_pi.2 fun i ↦ ?_
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ ↦ ?_
      exact ((hP i j).comp (differentiableOn_fst.const_smul ρ) fun zw (hzw : zw ∈ Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ) ↦ (hball _).2 hzw.1).mul
        (by fun_prop : Differentiable ℂ fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ zw.2 j).differentiableOn
    have := GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ) hφ
      fun zw hzw ↦ ⟨hsub _ hzw.1, Set.mem_univ _⟩
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun zw hzw ↦ ?_
    dsimp only
    rw [hchs, e.right_inv (hsub _ hzw.1)]
  · intro x hx
    have hxe := (hsrc x).1 hx
    have hhol : IsHolTo Set.univ (fun w ↦ (ex x w).left) := by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ ↦ (e x, w)) hjoint isOpen_univ
        ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w _ ↦ Set.mk_mem_prod (e.map_source hxe.1) (Set.mem_univ w)
      refine GlobalTheory.HolPeriods.isHolTo_congr this fun w _ ↦ ?_
      dsimp only
      rw [e.left_inv hxe.1]
    have hex : IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := ⟨hadd x hxe.1, (htan x hxe.1).1, (htan x hxe.1).2⟩
    have := isExpAt_mulVec H _ Z.t (x.1 ≫ genι Z) g (ex x) (P (e x)) (hPu _ hxe.2) hhol hex
    exact ⟨this.2.1, this.2.2⟩
  · intro x _
    rw [hch, smul_smul, mul_inv_cancel₀ hρ0, one_smul]

end GlobalTheory.ShFam.Hor.LogCh
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | exact GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  first | exact @GlobalTheory.posDef_im_on_ball_of_logExp | exact GlobalTheory.posDef_im_on_ball_of_logExp | (intros; apply GlobalTheory.posDef_im_on_ball_of_logExp <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem intGr_pointPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    intGr H Dw (pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  have hPsi : GlobalTheory.CompHt.fintypePsi (H := H) =
      (inferInstance : Fintype (GlobalTheory.AllWt.Psi H)) := Subsingleton.elim _ _
  unfold intGr
  rw [hPsi]
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    exact prod_Ioi_rev v

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold GlobalTheory.GoodMetric.rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  have h : antisymm (chernRoots Dw.mult (pointPoly H Dw) * fibrePoint Dw.mult) =
      chernRoots Dw.mult (pointPoly H Dw) * rootDiscr Dw.mult := by
    rw [antisymm_chernRoots_mul, antisymm_fibrePoint]
  rw [← h, degFl_rho_antisymm, prod_factorial_mult,
    rho_eq_flagMap, ← GlobalTheory.Schubert.schubGam_apply, GlobalTheory.SchubertPoint.schubGam_pointPoly, mul_one]
  have hne : ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H)) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)
  exact div_self hne

end GlobalTheory.GrassTop
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), IsWeightedHomogeneous Prod.snd Q (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) → ∃ c : ℝ, Q - C c * pointPoly H Dw ∈ relIdeal H Dw := by
  first | exact @GlobalTheory.GrassTopDim.top_eq_smul_point | exact GlobalTheory.GrassTopDim.top_eq_smul_point | (intros; apply GlobalTheory.GrassTopDim.top_eq_smul_point <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_eq_flagDegree_weight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ), D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) → antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) = chernRoots Dw.mult R * rootDiscr Dw.mult → intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  first | exact @GlobalTheory.GrassTop.intGr_eq_flagDeg | exact GlobalTheory.GrassTop.intGr_eq_flagDeg | (intros; apply GlobalTheory.GrassTop.intGr_eq_flagDeg <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical


theorem _root_.GlobalTheory.T.grassmannProductIntegral_eq_zero_of_mem_relIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Q ∈ relIdeal H Dw → intGr H Dw Q = 0 := by
  first | exact @GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | exact GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal | (intros; apply GlobalTheory.GrassTop.intGr_eq_zero_of_mem_relIdeal <;> assumption)
end
