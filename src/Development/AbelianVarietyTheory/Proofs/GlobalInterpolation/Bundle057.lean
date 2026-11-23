module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle056
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RpowLeExpRpowEventually
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 - η ≤ σ → σ ≤ 1 → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  first | exact @GlobalTheory.Lin.LogFree.zero_density | exact GlobalTheory.Lin.LogFree.zero_density | (intros; apply GlobalTheory.Lin.LogFree.zero_density <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZerosNearOne

theorem main : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, adm6 D C1 c := by
  obtain ⟨C, c, hC, hc, H⟩ := density_and_regions
  exact ⟨C, c, hC, hc, fun _ => H⟩

end GlobalTheory.ZerosNearOne
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZeroBounds

theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealAdeleCoord

theorem bijective_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {T : Type} (τ : T → (E →+* ℂ))
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) :
    Function.Bijective fun ρ => InfinitePlace.mk ((τ ρ).comp (algebraMap F E)) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  obtain ⟨δ, h0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  constructor
  · intro i j hij
    apply hτ.1
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' h0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff hij) with e | e
    · simp only [e]
    · simp only [e, InfinitePlace.mk_conjugate_eq]
  · intro w
    obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk (ComplexEmbedding.lift E w.embedding))
    refine ⟨i, ?_⟩
    have := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) hi
    simp only [InfinitePlace.comap_mk, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding] at this
    exact this

theorem exists_realCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ
  haveI hF := h.1
  let u : T ≃ InfinitePlace F := Equiv.ofBijective _ (bijective_place σ h τ hτ)
  let s : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hs : ∀ w, Continuous (s w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hs' : ∀ w, Continuous (s w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hsc : ∀ w x, ((s w x : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w x := fun w x =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) x
  let r : Ainf F ≃+* (T → ℝ) :=
    { toFun := fun a ρ => s (u ρ) (a (u ρ))
      invFun := fun y w => (s w).symm (y (u.symm w))
      left_inv := fun a => funext fun w => by
        obtain ⟨ρ, rfl⟩ := u.surjective w
        show (s (u ρ)).symm (s (u (u.symm (u ρ))) (a (u (u.symm (u ρ))))) = _
        rw [u.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv := fun y => funext fun ρ => by
        show s (u ρ) ((s (u ρ)).symm (y (u.symm (u ρ)))) = _
        rw [RingEquiv.apply_symm_apply, u.symm_apply_apply]
      map_mul' := fun a b => funext fun ρ => map_mul (s (u ρ)) (a (u ρ)) (b (u ρ))
      map_add' := fun a b => funext fun ρ => map_add (s (u ρ)) (a (u ρ)) (b (u ρ)) }
  have hr : ∀ a ρ, r a ρ = s (u ρ) (a (u ρ)) := fun _ _ => rfl
  refine ⟨r, continuous_pi fun ρ => (hs _).comp (continuous_apply (u ρ)),
    continuous_pi fun w => (hs' w).comp (continuous_apply (u.symm w)), fun a ρ => ?_, fun a => ?_, fun a => ?_⟩
  · rw [GlobalTheory.InfAdeleCM.hom_tmul _ _ (hθ ρ).1 (hθ ρ).2, map_one, mul_one, hr, hsc]
    rfl
  · unfold LocalAdditiveCharacterDual.stdInf
    rw [← Complex.exp_sum, ← u.sum_comp]
    congr 1
    simp only [← hsc, ← hr, Complex.ofReal_re]
    push_cast
    rw [← Finset.mul_sum]
    ring
  · constructor
    · intro ha ρ
      rw [hr]
      exact (map_ne_zero _).2 (ha _)
    · intro ha w
      obtain ⟨ρ, rfl⟩ := u.surjective w
      exact (map_ne_zero (s (u ρ))).1 (ha ρ)

end GlobalTheory.RealAdeleCoord
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem natCard_GL_zmod_le (r g : ℕ) (hg : 0 < g) :
    Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r * r) := by
  haveI : NeZero g := ⟨hg.ne'⟩
  have h1 : Nat.card (GL (Fin r) (ZMod g)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) :=
    Nat.card_le_card_of_injective _ Units.val_injective
  have h2 : Nat.card (Matrix (Fin r) (Fin r) (ZMod g)) = g ^ (r * r) := by
    show Nat.card (Fin r → Fin r → ZMod g) = _
    simp [Nat.card_fun, pow_mul]
  exact h2 ▸ h1

theorem log_levelGroup_le_and_level_large : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, lam0 (Fm.D x i) ≤ x ^ (15 : ℝ) ∧ 8 * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.r : ℝ) / ((min ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) : ℕ) : ℝ) ≤ 1 / 3 ∧ 1 ≤ (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := poly_sizes_ranks_weights eps Fm
  refine ⟨max x0 8, fun x hx hx1 i => ?_⟩
  obtain ⟨hCt, hf, hm, hk, -, -, -, hLx, -, hL1, hL2, hb, -⟩ :=
    hx0 x (le_trans (le_max_left _ _) hx) hx1 i
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLe := Fm.L_eps x i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have hb1 : 1 ≤ L.sc.b := le_trans (Real.one_le_rpow h1x (by linarith)) hb
  have h2m := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hfk : D.R.f ≤ D.R.k := D.R.f_le_k
  have hrk : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hk5 : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by omega
    exact_mod_cast this
  have hfk' : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrk' : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast hrk
  have hg8 : ∀ j, (D.R.k : ℝ) ^ 8 ≤ (D.host.g j : ℝ) := fun j =>
    le_trans (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hb1) 8) (hG j j).1
  have hkpos : (0 : ℝ) < (D.R.k : ℝ) ^ 8 := by positivity
  have hgpos : ∀ j, 0 < D.host.g j := fun j => by
    have := lt_of_lt_of_le hkpos (hg8 j)
    exact_mod_cast this
  have hlog : ∀ j, Real.log (D.host.g j : ℝ) ≤ x := fun j => by
    refine (hG j j).2.2.trans ?_
    unfold szTh Scale.L
    rw [hLx, hLe, ← Real.rpow_add h0x]
    calc x ^ (eps / 100 + eps) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  refine ⟨?_, ?_, hb1⟩
  · have hc : D.what₂.restRowsFiniteGroupCard ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by
      rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_pow, pow_mul _ (D.R.r * D.R.r),
        pow_mul _ (D.R.r * D.R.r)]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 0)) _)
        (Nat.pow_le_pow_left (natCard_GL_zmod_le _ _ (hgpos 1)) _)
    have hc' : (D.what₂.restRowsFiniteGroupCard : ℝ) ≤
        ((D.host.g 0 : ℝ) * D.host.g 1) ^ (D.R.r * D.R.r * D.R.f) := by exact_mod_cast hc
    have hp : (0 : ℝ) < D.what₂.restRowsFiniteGroupCard := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos
    have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast hgpos 0
    have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast hgpos 1
    have hr5 : (D.R.r : ℝ) ≤ 2 * x ^ (5 : ℝ) := by linarith
    unfold lam0
    refine (Real.log_le_log hp hc').trans ?_
    rw [Real.log_pow, Real.log_mul hg0.ne' hg1.ne']
    push_cast
    have hl0 : 0 ≤ Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
      add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    have hl2 : Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) ≤ 2 * x := by
      linarith [hlog 0, hlog 1]
    have e5 : x ^ (5 : ℝ) = x ^ 5 := by exact_mod_cast Real.rpow_natCast x 5
    have e3 : x ^ (3 : ℝ) = x ^ 3 := by exact_mod_cast Real.rpow_natCast x 3
    have e15 : x ^ (15 : ℝ) = x ^ 15 := by exact_mod_cast Real.rpow_natCast x 15
    rw [e5] at hr5
    rw [e3] at hf
    rw [e15]
    calc (D.R.r : ℝ) * D.R.r * D.R.f * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ))
        ≤ (2 * x ^ 5) * (2 * x ^ 5) * x ^ 3 * (2 * x) := by gcongr
      _ = 8 * x ^ 14 := by ring
      _ ≤ x * x ^ 14 := by gcongr
      _ = x ^ 15 := by ring
  · have hmin : (D.R.k : ℝ) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
      push_cast
      exact le_min (hg8 0) (hg8 1)
    rw [div_le_iff₀ (lt_of_lt_of_le hkpos hmin)]
    have h1 : 8 * (D.R.f : ℝ) * D.R.r ≤ 8 * (D.R.k : ℝ) * (2 * D.R.k) := by gcongr
    have h2 : (5 : ℝ) ^ 6 ≤ (D.R.k : ℝ) ^ 6 := by gcongr
    have h3 : (D.R.k : ℝ) ^ 8 = (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by ring
    have h4 : (5 : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 6 * (D.R.k : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (D.R.k : ℝ)]

end GlobalTheory
end
