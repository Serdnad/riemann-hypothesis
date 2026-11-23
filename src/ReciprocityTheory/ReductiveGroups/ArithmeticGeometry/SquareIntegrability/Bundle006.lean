module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle001
public import Formalism.FilteredPoleLength.LocalDescentLevels.DetMulEqSumPrincipal
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle001
public import Formalism.FilteredPoleLength.LocalDescentLevels.IntegralMulExpNegSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Metric

theorem sum_norm_smul_single {N : ℕ} (a : Fin N) (w : ℂ) :
    ∑ i, ‖(w • (Pi.single a (1 : ℂ) : Fin N → ℂ)) i‖ = ‖w‖ := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem contDiff_of_differentiable {N : ℕ} {F : (Fin N → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {n : WithTop ℕ∞} : ContDiff ℂ n F := by
  have hA := ReciprocityTheory.AnForm.Osgood.osgood N Set.univ F isOpen_univ hF.differentiableOn
  exact contDiffOn_univ.mp (hA.contDiffOn uniqueDiffOn_univ)

theorem iter_step_bound {N : ℕ} (F : (Fin N → ℂ) → ℂ) (hF : Differentiable ℂ F) (ρ M : ℝ)
    (hρ : 0 < ρ) : ∀ (k : ℕ) (l : Fin k → Fin N) (x : Fin N → ℂ),
    (∀ y, ∑ i, ‖y i - x i‖ ≤ k * ρ → ‖F y‖ ≤ M) →
    ‖iteratedFDeriv ℂ k F x (fun j => Pi.single (l j) 1)‖ ≤ M / ρ ^ k := by
  intro k
  induction k with
  | zero =>
    intro l x hM
    simpa only [iteratedFDeriv_zero_apply, pow_zero, div_one] using hM x (by simp)
  | succ k ih =>
    intro l x hM
    set e : Fin N → ℂ := Pi.single (l 0) 1 with he
    set v : Fin k → (Fin N → ℂ) := fun j => Pi.single (l (Fin.succ j)) 1 with hv
    set A := iteratedFDeriv ℂ k F with hA
    have hD : Differentiable ℂ A :=
      ContDiff.differentiable_iteratedFDeriv (m := k)
        (show ((k : ℕ) : WithTop ℕ∞) < ((k + 1 : ℕ) : WithTop ℕ∞) by exact_mod_cast Nat.lt_succ_self k)
        (contDiff_of_differentiable hF)
    set g : ℂ → ℂ := fun w => A (x + w • e) v with hg
    have hpath : ∀ w0 : ℂ, HasDerivAt (fun w : ℂ => x + w • e) e w0 := by
      intro w0
      have := ((hasDerivAt_id w0).smul_const e).const_add x
      simpa using this
    have hgd : ∀ w0 : ℂ, HasDerivAt g (fderiv ℂ A (x + w0 • e) e v) w0 := by
      intro w0
      have h1 := (hD (x + w0 • e)).hasFDerivAt.comp_hasDerivAt w0 (hpath w0)
      have h2 := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => Fin N → ℂ) ℂ v).hasFDerivAt.comp_hasDerivAt w0 h1
      simpa [Function.comp_def] using h2
    have hgdiff : Differentiable ℂ g := fun w0 => (hgd w0).differentiableAt
    have hderiv : deriv g 0 = iteratedFDeriv ℂ (k + 1) F x (fun j => Pi.single (l j) 1) := by
      rw [(hgd 0).deriv, iteratedFDeriv_succ_apply_left, zero_smul, add_zero]
      rfl
    have hsph : ∀ w ∈ sphere (0 : ℂ) ρ, ‖g w‖ ≤ M / ρ ^ k := by
      intro w hw
      have hw' : ‖w‖ = ρ := by simpa using hw
      have := ih (fun j => l (Fin.succ j)) (x + w • e) (by
        intro y hy
        apply hM y
        calc ∑ i, ‖y i - x i‖ ≤ ∑ i, (‖y i - (x + w • e) i‖ + ‖(w • e) i‖) := by
              apply Finset.sum_le_sum; intro i _
              have : y i - x i = (y i - (x + w • e) i) + (w • e) i := by simp; ring
              rw [this]; exact norm_add_le _ _
          _ = ∑ i, ‖y i - (x + w • e) i‖ + ρ := by
              rw [Finset.sum_add_distrib, he, sum_norm_smul_single, hw']
          _ ≤ k * ρ + ρ := by linarith
          _ = ((k + 1 : ℕ) : ℝ) * ρ := by push_cast; ring)
      simpa [hg, hA, hv] using this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hgdiff.diffContOnCl hsph
    rw [hderiv] at hc
    rw [pow_succ, ← div_div]
    exact hc

theorem cauchy_gauss_le {N k : ℕ} (F : (Fin N → ℂ) → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ z, ‖F z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S) (l : Fin k → Fin N) :
    ‖iteratedFDeriv ℂ k F 0 (fun j => Pi.single (l j) 1)‖ ≤
      Real.sqrt S * (Real.pi * Real.exp 1 * k) ^ ((k : ℝ) / 2) := by
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [iteratedFDeriv_zero_apply]
    have h0 := hS 0
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h0
    simpa using Real.abs_le_sqrt h0
  · have hπk : 0 < Real.pi * k := by positivity
    obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = 1 / Real.sqrt (Real.pi * k) := ⟨_, rfl⟩
    have hρ : 0 < ρ := by rw [hρd]; positivity
    have hρ2 : ρ ^ 2 = 1 / (Real.pi * k) := by rw [hρd, div_pow, Real.sq_sqrt hπk.le, one_pow]
    have hbound := iter_step_bound F hF ρ (Real.sqrt S * Real.exp ((k : ℝ) / 2)) hρ k l 0 (by
      intro y hy
      simp only [Pi.zero_apply, sub_zero] at hy
      have hsq : ∑ i, ‖y i‖ ^ 2 ≤ k / Real.pi :=
        calc ∑ i, ‖y i‖ ^ 2 ≤ (∑ i, ‖y i‖) ^ 2 :=
              Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
          _ ≤ (k * ρ) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _) hy 2
          _ = k / Real.pi := by
              rw [mul_pow, hρ2]; field_simp
      have h2 : ‖F y‖ ^ 2 ≤ S * Real.exp k := by
        have he : ‖F y‖ ^ 2 = ‖F y‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖y i‖ ^ 2)
            * Real.exp (Real.pi * ∑ i, ‖y i‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]; simp
        rw [he]
        calc _ ≤ S * Real.exp (Real.pi * ∑ i, ‖y i‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (hS y) (Real.exp_pos _).le
          _ ≤ S * Real.exp k := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hS0
              calc Real.pi * ∑ i, ‖y i‖ ^ 2 ≤ Real.pi * (k / Real.pi) :=
                    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
                _ = k := by field_simp
      have hsx : Real.sqrt S * Real.exp ((k : ℝ) / 2) = Real.sqrt (S * Real.exp k) := by
        have : Real.exp (k : ℝ) = Real.exp ((k : ℝ) / 2) ^ 2 := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [Real.sqrt_mul hS0, this, Real.sqrt_sq (Real.exp_pos _).le]
      rw [hsx]
      simpa using Real.abs_le_sqrt h2)
    refine hbound.trans (le_of_eq ?_)
    have hr : ρ ^ k = 1 / (Real.pi * k) ^ ((k : ℝ) / 2) := by
      rw [hρd, div_pow, one_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hπk.le]
      ring_nf
    rw [show Real.pi * Real.exp 1 * k = (Real.pi * k) * Real.exp 1 by ring,
      Real.mul_rpow hπk.le (Real.exp_pos 1).le, Real.exp_one_rpow, hr]
    field_simp

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2.Ext

theorem all : All :=
  ⟨Formalism.LatticeBaseChangeAlt.packingCount, Formalism.LatticeBaseChangeAlt.gaussian_tail_bound, Formalism.LatticeBaseChangeAlt.ballVolume, Formalism.LatticeBaseChangeAlt.gHadamard,
    Formalism.LatticeBaseChangeAlt.nearestPlane, Formalism.LatticeBaseChangeAlt.cauchyBinetMax, Formalism.LatticeBaseChangeAlt.detPerturbation,
    Formalism.LatticeBaseChangeAlt.detPerturbNumeric, Formalism.LatticeBaseChangeAlt.detProductRest⟩

end ReciprocityTheory.ChartRestriction.G.I2.Ext
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_covol_lb [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hG : Ext.GHadamard)
    (ob : OrthonormalBasis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I))
    (a : Fin (Module.finrank ℝ (IR I)) → IR I) (ha : ∀ i, (a i : Vsp X.dim) ∈ I)
    (hdet : ob.toBasis.det a ≠ 0) :
    1 ≤ |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph /
      (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
  unfold Ext.GHadamard at hG
  obtain ⟨x, u, hxu, hli, hnorm⟩ := hI.u1
  let u' : Fin (Module.finrank ℝ (IR I)) → IR I := fun j => ⟨u j, (hxu j).2.1⟩
  have hli' : LinearIndependent ℝ u' := LinearIndependent.of_comp (IR I).subtype (by exact hli)
  have hU : IsUnit (ob.toBasis.det u') := by
    rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ (IR I))) with hE | hN
    · rw [Module.Basis.det_apply, Matrix.det_isEmpty]
      exact isUnit_one
    · have hspan : Submodule.span ℝ (Set.range u') = ⊤ :=
        hli'.span_eq_top_of_card_eq_finrank (by simp)
      have hU' := ob.toBasis.isUnit_det (Module.Basis.mk hli' hspan.ge)
      rwa [Module.Basis.coe_mk] at hU'
  have hint : ∀ j k, ∃ m : ℤ, (Hf (x j) (a k : Vsp X.dim)).im = m := fun j k =>
    X.integral _ _ (hxu j).1 (hI.le (ha k))
  let Gz : Matrix (Fin (Module.finrank ℝ (IR I))) (Fin (Module.finrank ℝ (IR I))) ℤ :=
    fun j k => (hint j k).choose
  have hGjk : ∀ j k, inner ℝ (u' j) (a k) = (Gz j k : ℝ) := fun j k => by
    show _ = (((hint j k).choose : ℤ) : ℝ)
    rw [← (hint j k).choose_spec]
    exact (hxu j).2.2 _ (a k).2
  have hmat : Matrix.transpose (ob.toBasis.toMatrix u') * ob.toBasis.toMatrix a = Gz.map (fun m : ℤ => (m : ℝ)) := by
    ext j k
    rw [Matrix.mul_apply, Matrix.map_apply, ← hGjk j k]
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← OrthonormalBasis.sum_inner_mul_inner ob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (u' j) (ob i)]
  have hdetG : ob.toBasis.det u' * ob.toBasis.det a = ((Gz.det : ℤ) : ℝ) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_transpose (ob.toBasis.toMatrix u'),
      ← Matrix.det_mul, hmat]
    first
      | exact (Int.cast_det Gz).symm
      | exact (RingHom.map_det (Int.castRingHom ℝ) Gz).symm
      | simp [Int.cast_det]
  have hGz : Gz.det ≠ 0 := by
    intro h0
    have h00 : ob.toBasis.det u' * ob.toBasis.det a = 0 := by rw [hdetG, h0, Int.cast_zero]
    rcases mul_eq_zero.mp h00 with h | h
    · exact hU.ne_zero h
    · exact hdet h
  have h1 : (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := by
    rw [← abs_mul, hdetG]
    exact_mod_cast Int.one_le_abs hGz
  have hH := hG (Module.finrank ℝ (IR I)) (ob.toBasis.toMatrix u')
  rw [← Module.Basis.det_apply] at hH
  have hcol : ∀ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) := fun j => by
    apply Real.sqrt_le_sqrt
    have hn : ∑ i, ob.toBasis.toMatrix u' i j ^ 2 = ‖u j‖ ^ 2 := by
      have hu : ‖u j‖ = ‖u' j‖ := rfl
      simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
      rw [hu, ← ob.repr.norm_map (u' j), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact hnorm j
  have hprod : ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤
      Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
    calc ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2)
        ≤ ∏ _j : Fin (Module.finrank ℝ (IR I)), Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) :=
          Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hcol j)
      _ = Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := h1
    _ ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) * |ob.toBasis.det a| :=
      mul_le_mul_of_nonneg_right (hH.trans hprod) (abs_nonneg _)
    _ = |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := mul_comm _ _

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure TorusAt (X : Data E r) (x : Frame X.Ψ r) where
  T : PT E
  φ : (Fin r → E) →+ Vsp T.dim
  sg : ℝ
  sg_pm : sg = 1 ∨ sg = -1

  dim_pos : ∀ τ : X.Ψ, T.dim τ.1 = X.p0
  dim_neg : ∀ τ : X.Ψ, T.dim (ComplexEmbedding.conjugate τ.1) = r - X.p0

  e : X.Ψ → Fin r → (Fin r → ℂ)
  e_orth : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0
  e_flag : ∀ τ (i : ℕ) (hi : i ≤ r),
    Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) =
      Submodule.span ℂ (Set.range fun a : Fin i => col (mat x τ) (Fin.castLE hi a))

  coord_pos : ∀ (τ : X.Ψ) (a : Fin (T.dim τ.1)) (v : Fin r → E),
    (φ v) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (Data.emb τ.1 v) (e τ (Fin.castLE (by rw [dim_pos τ]; exact X.p0_le) a))
  coord_neg : ∀ (τ : X.Ψ) (a : Fin (T.dim (ComplexEmbedding.conjugate τ.1))) (v : Fin r → E),
    (φ v) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      (starRingEnd ℂ) (-hermC τ.1 X.Gm (Data.emb τ.1 v)
        (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (dim_neg τ); have := X.p0_le; omega⟩))
  lat : ∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y
  act_eq : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)
  im_eq : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
    sg * ((Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) : ℚ) : ℝ)

  w0 : 𝓞 E
  eps_eq : ∀ v ∈ X.Λ, (T.eps (φ v) : ℝ) = Real.cos (Real.pi * (Hf (φ v) (φ ((w0 : E) • v))).im)

  s : (Fin 1 → Vsp T.dim) → ℂ
  s_mem : s ∈ T.Sec 1 1
  s_ne : s ≠ 0

def TorusAtExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ φ : X.Λ →+ ℤ, ∃ u ∈ X.Λ, ∀ v : X.Λ,
      (φ v : ℚ) = Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (v : Fin r → E))) →
    ∀ w0 : 𝓞 E, (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) →
    ∀ x ∈ X.dom, ∃ A : TorusAt X x, A.w0 = w0

def TorusAtIsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (A : TorusAt X x), IsTorusAt X x A.T

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

section basic

variable {ι : Type} [Fintype ι]

private theorem Hf_eq_inner_swap_complex (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp [Hf, PiLp.inner_apply, RCLike.inner_apply]

private theorem real_inner_eq_re_inner' (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (inner ℂ x y).re := by
  first
  | exact real_inner_eq_re_inner ℂ x y
  | simp [PiLp.inner_apply, Complex.inner, Complex.re_sum, RCLike.inner_apply, mul_comm]

theorem Hf_conj (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  rw [Hf_eq_inner_swap_complex, Hf_eq_inner_swap_complex]
  exact (inner_conj_symm _ _).symm

theorem real_inner_eq_Hf (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫_ℝ = (Hf y x).re := by
  rw [Hf_eq_inner_swap_complex, real_inner_eq_re_inner']

theorem Hf_im_eq (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪Complex.I • w, v⟫_ℝ := by
  rw [real_inner_eq_re_inner', inner_smul_left, Hf_eq_inner_swap_complex]
  simp

theorem Hf_im_eq' (v w : EuclideanSpace ℂ ι) : (Hf v w).im = ⟪-(Complex.I • v), w⟫_ℝ := by
  rw [Hf_conj w v, Complex.conj_im, Hf_im_eq w v, inner_neg_left]

theorem Hf_im_antisymm (v w : EuclideanSpace ℂ ι) : (Hf v w).im = -(Hf w v).im := by
  rw [Hf_conj w v, Complex.conj_im]

theorem Hf_im_add_left (v v' w : EuclideanSpace ℂ ι) :
    (Hf (v + v') w).im = (Hf v w).im + (Hf v' w).im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_right, Complex.add_im]

theorem Hf_im_add_right (v w w' : EuclideanSpace ℂ ι) :
    (Hf v (w + w')).im = (Hf v w).im + (Hf v w').im := by
  simp only [Hf_eq_inner_swap_complex, inner_add_left, Complex.add_im]

theorem Hf_im_smul_left (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_assoc]

theorem Hf_im_smul_right (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  simp [Hf, Complex.im_sum, Finset.mul_sum, mul_left_comm]

theorem Hf_im_zero_left (w : EuclideanSpace ℂ ι) : (Hf 0 w).im = 0 := by
  simp [Hf]

theorem Hf_im_zero_right (v : EuclideanSpace ℂ ι) : (Hf v 0).im = 0 := by
  simp [Hf]

theorem abs_Hf_im_le (v w : EuclideanSpace ℂ ι) : |(Hf v w).im| ≤ ‖v‖ * ‖w‖ := by
  rw [Hf_eq_inner_swap_complex, mul_comm]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm w v)

theorem Hf_im_span_left (S : Set (EuclideanSpace ℂ ι)) (w : EuclideanSpace ℂ ι)
    (h : ∀ v ∈ S, (Hf v w).im = 0) : ∀ v ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_left w
  | add x y _ _ hx hy => rw [Hf_im_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_left, hx, mul_zero]

theorem Hf_im_span_right (S : Set (EuclideanSpace ℂ ι)) (v : EuclideanSpace ℂ ι)
    (h : ∀ w ∈ S, (Hf v w).im = 0) : ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_right v
  | add x y _ _ hx hy => rw [Hf_im_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_right, hx, mul_zero]

theorem Hf_im_span_iso (S : Set (EuclideanSpace ℂ ι)) (h : ∀ v ∈ S, ∀ w ∈ S, (Hf v w).im = 0) :
    ∀ v ∈ Submodule.span ℝ S, ∀ w ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv w hw
  exact Hf_im_span_right S v (fun w' hw' => Hf_im_span_left S w' (fun v' hv' => h v' hv' w' hw') v hv) w hw

end basic

variable {E : Type} [Field E] [NumberField E]

section vecU

variable {dim : (E →+* ℂ) → ℕ}

theorem exists_isU (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) : ∃ u, IsU I x u := by
  let K := IR I
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun a => (Hf x (a : Vsp dim)).im
      map_add' := fun a b => by simp only [Submodule.coe_add, Hf_im_add_right]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Hf_im_smul_right, smul_eq_mul, RingHom.id_apply] }
  let u : K := (InnerProductSpace.toDual ℝ K).symm (LinearMap.toContinuousLinearMap f)
  refine ⟨(u : Vsp dim), u.2, fun a ha => ?_⟩
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := K) (x := ⟨a, ha⟩)
    (y := LinearMap.toContinuousLinearMap f)
  exact h1

theorem IsU.unique {I : Submodule ℤ (Vsp dim)} {x u u' : Vsp dim} (h : IsU I x u)
    (h' : IsU I x u') : u = u' := by
  have hd : u - u' ∈ IR I := Submodule.sub_mem _ h.1 h'.1
  have h0 : inner ℝ (u - u') (u - u') = (0 : ℝ) := by
    rw [inner_sub_left, h.2 _ hd, h'.2 _ hd, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem IsU.norm_sq {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    ‖u‖ ^ 2 = (Hf x u).im := by
  rw [← real_inner_self_eq_norm_sq, h.2 u h.1]

theorem IsU.eq_zero_iff {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    u = 0 ↔ ∀ a ∈ I, (Hf x a).im = 0 := by
  constructor
  · rintro rfl a ha
    rw [← h.2 a (Submodule.subset_span ha), inner_zero_left]
  · intro hI
    have hs := Hf_im_span_right (I : Set (Vsp dim)) x (fun w hw => hI w hw) u h.1
    have h0 : inner ℝ u u = (0 : ℝ) := by rw [h.2 u h.1, hs]
    exact inner_self_eq_zero.1 h0

theorem mem_IR {I : Submodule ℤ (Vsp dim)} {x : Vsp dim} (h : x ∈ I) : x ∈ IR I := Submodule.subset_span h

end vecU

end

end ReciprocityTheory.ChartRestriction.G.I2
end
