module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Polynomial

namespace GlobalTheory.UnitaryCongruenceDet

noncomputable section

def ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_eq (x : E) : cc x = ccHom E x := rfl

theorem transpose_mul_mul_map {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γᵀ * G * γ.map (ccHom E) = G := by
  ext i j
  have hs : ∀ k, γ *ᵥ Pi.single k 1 = fun a => γ a k := by
    intro k; funext a; simp [mulVec, dotProduct, Pi.single_apply]
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [herm, cc_eq, hs] at hij
  simp only [Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, hij]
  simp [Pi.single_apply]

theorem det_mul_cc_det {r : ℕ} (G γ : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) :
    γ.det * cc γ.det = 1 := by
  have e := congrArg Matrix.det (transpose_mul_mul_map G γ h)
  have hd : (γ.map (ccHom E)).det = ccHom E γ.det := by rw [RingHom.map_det]; rfl
  rw [det_mul, det_mul, det_transpose, hd] at e
  rw [cc_eq]
  apply mul_right_cancel₀ hG
  linear_combination e

theorem isIntegral_of_left_eigen {r : ℕ} {Ω : Type} [Field Ω] [Algebra E Ω]
    (C : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (hC : ∀ x ∈ Λ, C *ᵥ x ∈ Λ)
    (μ : Ω) (u : Fin r → Ω) (hu : u ≠ 0) (hμ : u ᵥ* C.map (algebraMap E Ω) = μ • u) :
    IsIntegral ℤ μ := by
  classical
  let φ := algebraMap E Ω
  let g : (Fin r → E) →ₗ[E] Ω :=
    { toFun := fun x => u ⬝ᵥ (fun a => φ (x a))
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add (f := _)]
        rw [← dotProduct_add]; rfl
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring }
  let N : Submodule ℤ Ω := (Λ.restrictScalars ℤ).map (g.restrictScalars ℤ)
  have hNfg : N.FG := (Submodule.FG.restrictScalars (R := ℤ) hfg).map _
  have hN : N ≠ ⊥ := by
    intro hN
    apply hu
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      intro x hx
      have : g x ∈ N := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      rw [hN, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker] at this
    simpa [g, φ, dotProduct, Pi.single_apply, apply_ite] using this
  refine isIntegral_of_smul_mem_submodule N hN hNfg μ ?_
  rintro n hn
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨C *ᵥ x, hC x hx, ?_⟩
  change u ⬝ᵥ (fun a => φ ((C *ᵥ x) a)) = μ • (u ⬝ᵥ fun a => φ (x a))
  have h1 : (fun a => φ ((C *ᵥ x) a)) = C.map φ *ᵥ (fun a => φ (x a)) := by
    funext a; exact RingHom.map_mulVec φ C x a
  rw [h1, dotProduct_mulVec, hμ, smul_dotProduct, smul_eq_mul]

theorem prod_eq_one_add {Ω : Type} [Field Ω] (M : ℕ) (hM : (M : Ω) ≠ 0) (s : Multiset Ω)
    (hs : ∀ l ∈ s, IsIntegral ℤ ((l - 1) / (M : Ω))) :
    ∃ z : Ω, IsIntegral ℤ z ∧ s.prod = 1 + M * z := by
  have hMint : IsIntegral ℤ (M : Ω) := by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ Ω (M : ℤ)))
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | cons a s ih =>
    obtain ⟨z, hz, hprod⟩ := ih (fun l hl => hs l (Multiset.mem_cons_of_mem hl))
    have ha := hs a (Multiset.mem_cons_self a s)
    set w := (a - 1) / (M : Ω) with hw
    have ha' : a = 1 + M * w := by rw [hw]; field_simp; ring
    refine ⟨w + z + M * w * z, (ha.add hz).add ((hMint.mul ha).mul hz), ?_⟩
    rw [Multiset.prod_cons, hprod, ha']
    ring

theorem det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r),
    3 ≤ M →
    (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) →
    ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M X hM hΓ γ hγ
  classical
  obtain ⟨⟨hherm, -⟩, hcong⟩ := (hΓ γ).1 hγ
  set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hM0 : (M : AlgebraicClosure E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hME : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  set A : Matrix (Fin r) (Fin r) E := (M : E)⁻¹ • (g - 1) with hA
  have hAΛ : ∀ x ∈ X.Λ, A *ᵥ x ∈ X.Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcong x hx
    have : A *ᵥ x = y := by
      rw [hA, smul_mulVec, sub_mulVec, one_mulVec, hxy, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, inv_mul_cancel₀ hME, one_smul]
    rw [this]; exact hy
  have hAmap : A.map φ = (M : AlgebraicClosure E)⁻¹ • (g.map φ - 1) := by
    ext i j
    by_cases hij : i = j <;> simp [hA, Matrix.one_apply, hij]
  have hroot : ∀ l ∈ (g.map φ).charpoly.roots, IsIntegral ℤ ((l - 1) / (M : AlgebraicClosure E)) := by
    intro l hl
    have hdet : (scalar (Fin r) l - g.map φ).det = 0 := by
      rw [← Matrix.eval_charpoly]; exact (mem_roots'.1 hl).2
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply isIntegral_of_left_eigen A X.Λ X.Λ_fg X.Λ_span hAΛ _ u hu
    have hgu : u ᵥ* g.map φ = l • u := by
      rw [vecMul_sub, sub_eq_zero] at hu0
      rw [← hu0]
      funext j
      simp [scalar_apply, vecMul_diagonal, mul_comm]
    rw [hAmap, vecMul_smul, vecMul_sub, vecMul_one, hgu]
    funext j
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  obtain ⟨z, hz, hprod⟩ := prod_eq_one_add M hM0 _ hroot
  have hφdet : φ g.det = 1 + M * z := by
    rw [RingHom.map_det, ← hprod]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hint : IsIntegral ℤ ((g.det - 1) / (M : E)) := by
    have h1 : φ ((g.det - 1) / (M : E)) = z := by
      rw [map_div₀, map_sub, map_one, map_natCast, hφdet]; field_simp; ring
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).1 (by change IsIntegral ℤ (φ _); rw [h1]; exact hz)
  have hc := det_mul_cc_det X.Gm g X.Gm_det hherm
  by_contra hne
  have hx : (⟨(g.det - 1) / M, hint⟩ : 𝓞 E) ≠ 0 := by
    intro h
    have : (g.det - 1) / (M : E) = 0 := congrArg Subtype.val h
    rcases div_eq_zero_iff.1 this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hME h
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hx
  have hσ' : 1 ≤ ‖σ ((g.det - 1) / M)‖ := hσ
  have h1 : ‖σ g.det‖ = 1 := by
    have := congrArg (fun z => ‖σ z‖) hc
    simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
      Complex.norm_conj] at this
    nlinarith [norm_nonneg (σ g.det)]
  rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast] at hσ'
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : ‖σ g.det - 1‖ ≤ 2 := by
    have := norm_sub_le (σ g.det) 1
    rw [h1, norm_one] at this
    linarith
  rw [le_div_iff₀ (by linarith)] at hσ'
  linarith

end

end GlobalTheory.UnitaryCongruenceDet
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

noncomputable section

theorem countable_GL_numberField {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable
    (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h

theorem continuous_mat_lact {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (g : GL (Fin r) E) (τ : Ψ) :
    Continuous fun z : Frame Ψ r => mat (lact g z) τ := by
  have h : Continuous fun z : Frame Ψ r => mat z τ := continuous_apply τ
  exact continuous_const.matrix_mul h

theorem baire_one_candidate {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)) :
    IsOpen W → W.Nonempty → W ⊆ X.dom →
    (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) →
    ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧
      ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  intro hW hne hWdom hmove
  let C : GL (Fin r) E → Set (Frame X.Ψ r) := fun g => {z | ∀ τ : X.Ψ, ∀ p q : Fin r, q < p →
    ((mat (lact (g * a) z) τ).adjugate * mat (lact c z) τ) p q = 0}
  have hC : ∀ g, IsClosed (C g) := by
    intro g
    simp only [C, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq ((((continuous_mat_lact (g * a) τ).matrix_adjugate).matrix_mul
      (continuous_mat_lact c τ)).matrix_elem p q) continuous_const
  have cover : ∀ z ∈ W, ∃ γ ∈ S, z ∈ C γ := by
    intro z hz
    obtain ⟨γ, hγ, b, hb, heq⟩ := hmove z hz
    refine ⟨γ, hγ, fun τ p q hqp => ?_⟩
    have key : mat (lact c z) τ = mat (lact (γ * a) z) τ * mat b τ := by
      have h1 : mat (lact c z) τ =
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat z τ)) * mat b τ := congrFun heq τ
      rw [h1]
      show _ = (((γ * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) * mat b τ
      rw [Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    have : mat b τ p q = 0 := (hb τ).2 p q hqp
    rw [this, mul_zero]
  haveI : Countable (GL (Fin r) E) := countable_GL_numberField r
  let f : Option S → Set (Frame X.Ψ r) := fun o => o.elim Wᶜ (fun γ => C γ.1)
  have hf : ∀ o, IsClosed (f o) := by
    rintro (_ | γ)
    exacts [hW.isClosed_compl, hC γ.1]
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ W
    · obtain ⟨γ, hγ, hzC⟩ := cover z hz
      exact Set.mem_iUnion.2 ⟨some ⟨γ, hγ⟩, hzC⟩
    · exact Set.mem_iUnion.2 ⟨none, hz⟩
  have hD := dense_iUnion_interior_of_closed hf hU
  obtain ⟨z, hzW, hz⟩ := hD.inter_open_nonempty W hW hne
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hz
  cases o with
  | none => exact absurd hzW (interior_subset ho)
  | some γ =>
    refine ⟨γ.1, γ.2, W ∩ interior (C γ.1), hW.inter isOpen_interior, ⟨z, hzW, ho⟩,
      fun x hx => hWdom hx.1, fun x hx => ?_⟩
    have hxd : x ∈ X.dom := hWdom hx.1
    have hxC : x ∈ C γ.1 := interior_subset hx.2
    simp only [C, Set.mem_setOf_eq] at hxC
    generalize γ.1 * a = g at hxC ⊢
    have hdetg : ∀ (g' : GL (Fin r) E) (τ : X.Ψ),
        ((g' : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
      intro g' τ
      have h := RingHom.map_det τ.1 (g' : Matrix (Fin r) (Fin r) E)
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units g').ne_zero
    have hdetx : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun τ => (hxd τ).1
    have hdetA : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), (mat (lact g' x) τ).det ≠ 0 := by
      intro g' τ
      show ((g' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hdetg g' τ) (hdetx τ)
    let b : Frame X.Ψ r := fun τ =>
      ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨b, fun τ => ⟨?_, fun p q hqp => ?_⟩, ?_⟩
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero
        (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdetA g τ))).ne_zero (hdetA c τ)
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ) p q = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hxC τ p q hqp, smul_zero]
    · funext τ
      have hginv : ((g : Matrix (Fin r) (Fin r) E).map τ.1)⁻¹ =
          ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 := by
        apply Matrix.inv_eq_right_inv
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      show ((g⁻¹ * c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        mat x τ * (((g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)⁻¹ *
          ((c : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))
      rw [Matrix.mul_inv_rev, hginv, Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (mat x τ) (mat x τ)⁻¹,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdetx τ)), Matrix.one_mul]

end

end GlobalTheory
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem linearIndependent_of_skew_of_real : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 →
    ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) →
    LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  intro E _ _ _ r n G hG e he hF
  have cc_mul' : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add' : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc' : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x

  have hmap : ∀ g : Fin n → E, (∑ i, g i • e i).map cc = ∑ i, cc (g i) • (e i).map cc := by
    intro g
    ext a b

    simp [Matrix.sum_apply, cc, map_sum]
  have hinj : ∀ M : Matrix (Fin r) (Fin r) E, Mᵀ * G = 0 → M = 0 := by
    intro M hM
    have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
    have h0 : Mᵀ = 0 := by
      have := congrArg (· * G⁻¹) hM
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu] using this
    simpa using congrArg Matrix.transpose h0
  have key : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∑ i, cc (g i) • e i = 0 := by
    intro g hg
    apply hinj
    have h2 : G * (∑ i, g i • e i).map cc = 0 := by
      rw [hg]
      ext a b
      simp [Matrix.mul_apply, cc]
    rw [hmap, Finset.mul_sum] at h2
    have h3 : (∑ i, cc (g i) • e i)ᵀ * G = - ∑ i, G * (cc (g i) • (e i).map cc) := by
      rw [Matrix.transpose_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left (he i)
    rw [h3, h2, neg_zero]

  have real : ∀ g : Fin n → E, (∀ i, cc (g i) = g i) → ∑ i, g i • e i = 0 → ∀ i, g i = 0 := by
    intro g hc hg i
    have hm : ∀ i, g i ∈ maximalRealSubfield E := fun i =>
      (IsCMField.complexConj_eq_self_iff E _).mp (hc i)
    have := Fintype.linearIndependent_iff.mp hF (fun i => ⟨g i, hm i⟩) hg i
    simpa using congrArg (Subtype.val) this
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hx' : cc x ≠ x := hx

  have sum_real : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∀ i, g i + cc (g i) = 0 := by
    intro g hg
    apply real
    · intro i
      rw [cc_add', cc_cc', add_comm]
    · simp only [add_smul, Finset.sum_add_distrib, hg, key g hg, add_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := sum_real g hg i
  have hxg : ∑ i, (x * g i) • e i = 0 := by
    simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have h2 := sum_real (fun i => x * g i) hxg i
  simp only [cc_mul'] at h2
  have h3 : cc (g i) = - g i := eq_neg_of_add_eq_zero_right h1
  rw [h3] at h2
  have h4 : (x - cc x) * g i = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hx'
  · exact h

end GlobalTheory
end
