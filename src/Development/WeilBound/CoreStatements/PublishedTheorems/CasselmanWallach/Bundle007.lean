module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace KInvarianceAlt

theorem kinv {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : ∃ k' ∈ Kset ε, k' * k = 1 := by
  obtain ⟨hu, hJ⟩ := hk
  have hu' : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu; rwa [Matrix.star_eq_conjTranspose] at this
  have hJh : (Jm ε)ᴴ = Jm ε := by
    ext i j; simp only [Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have h := congrArg Matrix.conjTranspose hJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hs' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have := Unitary.star_mem hu; rwa [Matrix.star_eq_conjTranspose] at this
  exact ⟨kᴴ, ⟨hs', hJ'⟩, hu'⟩

end KInvarianceAlt

theorem e1a : SmoothSeminormGrowth := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ i
  obtain ⟨q, N, hq, hg⟩ := hπ.growth i
  haveI : Nonempty (UJset ε) := ⟨⟨1, one_mem_UJ ε⟩⟩
  set W : Mx n → ℝ := fun g => (1 + hs g) ^ N with hWdef
  have hW : ∀ g, 0 < W g := fun g => pow_pos (by linarith [hs_nonneg g]) _
  have hWm : ∀ a b : Mx n, W (a * b) ≤ W a * W b := fun a b => by
    simp only [hWdef]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [hs_nonneg (a * b)]) (one_add_hs_mul_le a b) N
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ x, π (a * b) x = π a (π b x) := fun a ha b hb x => by
    rw [hπ.map_mul a ha b hb]; rfl
  let f : UJset ε → Seminorm ℂ E := fun g => (Real.toNNReal (W g.1)⁻¹) • (p i).comp (π g.1 : E →ₗ[ℂ] E)
  have hf : ∀ g x, f g x = p i (π g.1 x) / W g.1 := fun g x => by
    show ((Real.toNNReal (W g.1)⁻¹ : NNReal) : ℝ) * p i (π g.1 x) = _
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (hW _).le), div_eq_inv_mul]
  have hfq : ∀ g x, f g x ≤ q x := fun g x => by
    rw [hf, div_le_iff₀ (hW _), mul_comm]
    exact hg g.1 g.2 x
  have hbdd : BddAbove (Set.range f) := ⟨q, by
    rintro _ ⟨g, rfl⟩
    exact Pi.le_def.2 fun x => hfq g x⟩
  have hfb : ∀ x, BddAbove (Set.range fun g => f g x) := fun x => ⟨q x, by
    rintro _ ⟨g, rfl⟩
    exact hfq g x⟩
  set Q : Seminorm ℂ E := ⨆ g, f g with hQdef
  have hQ : ∀ x, Q x = ⨆ g, f g x := fun x => Seminorm.iSup_apply hbdd
  have hle : ∀ g x, f g x ≤ Q x := fun g x => by rw [hQ]; exact le_ciSup (hfb x) g
  have hQq : Q ≤ q := Pi.le_def.2 fun x => by rw [hQ]; exact ciSup_le fun g => hfq g x
  have h1 : ∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ W g * Q x := fun g hg x => by
    have := hle ⟨g, hg⟩ x
    rw [hf, div_le_iff₀ (hW _)] at this
    linarith
  have hKk : ∀ k ∈ Kset ε, ∀ x, Q (π k x) ≤ Q x := fun k hk x => by
    rw [hQ (π k x)]
    refine ciSup_le fun g => ?_
    have hgk : g.1 * k ∈ UJset ε := mul_mem_UJ g.2 (K_le_UJ hk)
    have := hle ⟨g.1 * k, hgk⟩ x
    rw [hf] at this ⊢
    have e : W (g.1 * k) = W g.1 := by
      simp only [hWdef, ((Formalism.REAL.hermitian_small_ball n ε).2 g.1 k hk).1]
    rw [← hmul g.1 g.2 k (K_le_UJ hk), ← e]
    exact this
  refine ⟨Q, N, Seminorm.continuous_of_le hq hQq, h1, fun h hh x => ?_, fun k hk x => ?_⟩
  · rw [hQ (π h x)]
    refine ciSup_le fun g => ?_
    rw [hf, hmul g.1 g.2 h hh x |>.symm, div_le_iff₀ (hW _)]
    calc p i (π (g.1 * h) x) ≤ W (g.1 * h) * Q x := h1 _ (mul_mem_UJ g.2 hh) x
      _ ≤ (W g.1 * W h) * Q x := mul_le_mul_of_nonneg_right (hWm _ _) (apply_nonneg _ _)
      _ = W h * Q x * W g.1 := by ring
  · refine le_antisymm (hKk k hk x) ?_
    obtain ⟨k', hk', e⟩ := KInvarianceAlt.kinv hk
    have := hKk k' hk' (π k x)
    rwa [← hmul k' (K_le_UJ hk') k (K_le_UJ hk), e, hπ.map_one] at this

end PositivityTheory.CW

end
end

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.CW

namespace BilinearFormCasimir

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

def tr (k : KG ε) (v : kfin ε σ) : kfin ε σ :=
  ⟨σ (toMK k⁻¹) v, isKFin_translate (mem_kfin.1 v.2) (toMK_mem_K _)⟩

theorem tr_add (k : KG ε) (v v' : kfin ε σ) : tr k (v + v') = tr k v + tr k v' :=
  Subtype.ext (map_add (σ (toMK k⁻¹)) (v : H) v')

theorem tr_smul (k : KG ε) (c : ℂ) (v : kfin ε σ) : tr k (c • v) = c • tr k v :=
  Subtype.ext (map_smul (σ (toMK k⁻¹)) c (v : H))

theorem continuous_tr (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v : kfin ε σ) :
    Continuous fun k : KG ε => l (tr k v) := by
  obtain ⟨S, hSf, hvS, hSK⟩ := mem_kfin.1 v.2
  haveI := hSf
  have hSk : ∀ x ∈ S, x ∈ kfin ε σ := fun x hx => mem_kfin.2 ⟨S, hSf, hx, hSK⟩
  let ι : S →ₗ[ℂ] kfin ε σ :=
    { toFun := fun x => ⟨x, hSk x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hc : Continuous (l ∘ₗ ι) := LinearMap.continuous_of_finiteDimensional _
  have hmem : ∀ k : KG ε, σ (toMK k⁻¹) v ∈ S := fun k => hSK _ (toMK_mem_K _) _ hvS
  have h1 : Continuous fun k : KG ε => σ (toMK k⁻¹) (v : H) :=
    (hU.2.2 v).comp_continuous ((continuous_toMK ε).comp continuous_inv) fun k => K_le_UJ (toMK_mem_K _)
  have h2 : Continuous fun k : KG ε => (⟨σ (toMK k⁻¹) v, hmem k⟩ : S) := h1.subtype_mk _
  exact (hc.comp h2).congr fun k => rfl

def fm (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) : ℂ := ∫ k, conj (l (tr k v)) * l (tr k y) ∂(muK ε)

theorem integrable_fm (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    Integrable (fun k : KG ε => conj (l (tr k v)) * l (tr k y)) (muK ε) := by
  haveI : CompactSpace (KG ε) := instCompactKG n ε
  have hc : Continuous fun k : KG ε => conj (l (tr k v)) * l (tr k y) :=
    ((continuous_tr hU l v).star).mul (continuous_tr hU l y)
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def bf (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fm l)
    (fun v v' y => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v' y)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), add_mul])
    (fun c v y => by
      unfold fm
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul, map_mul]
      ring)
    (fun v y y' => by
      unfold fm
      rw [← integral_add (integrable_fm hU l v y) (integrable_fm hU l v y')]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_add, map_add (f := _), mul_add])
    (fun c v y => by
      unfold fm
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [tr_smul, map_smul, smul_eq_mul]
      ring)

theorem bf_apply (hU : IsURepOn (UJset ε) σ) (l : kfin ε σ →ₗ[ℂ] ℂ) (v y : kfin ε σ) :
    bf hU l v y = fm l v y := rfl

end BilinearFormCasimir

open BilinearFormCasimir in
theorem e2b : E2b := by
  intro n ε H _ _ _ σ hU hI Q hQ v₀ hv₀
  have hv0 : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])

  let f0 : (ℂ ∙ v₀) →ₗ[ℂ] ℂ := (LinearPMap.mkSpanSingleton v₀ ((Q v₀ : ℝ) : ℂ) hv0).toFun
  have hf0 : ∀ x : (ℂ ∙ v₀), ‖f0 x‖ ≤ Q x := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have e : f0 ⟨c • v₀, hx⟩ = c • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ c hx
    rw [e, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
    exact (map_smul_eq_mul Q c v₀).symm.le
  obtain ⟨l, hl, hlQ⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ v₀) f0 hf0
  have hlv : l v₀ = ((Q v₀ : ℝ) : ℂ) := by
    have h1 : v₀ ∈ (ℂ ∙ v₀) := Submodule.mem_span_singleton_self v₀
    have h1' : (1 : ℂ) • v₀ ∈ (ℂ ∙ v₀) := by rw [one_smul]; exact h1
    rw [hl ⟨v₀, h1⟩]
    have e : f0 ⟨(1 : ℂ) • v₀, h1'⟩ = (1 : ℂ) • ((Q v₀ : ℝ) : ℂ) :=
      LinearPMap.mkSpanSingleton'_apply v₀ ((Q v₀ : ℝ) : ℂ) _ 1 h1'
    have e' : (⟨v₀, h1⟩ : (ℂ ∙ v₀)) = ⟨(1 : ℂ) • v₀, h1'⟩ := Subtype.ext (one_smul ℂ v₀).symm
    rw [e', e, one_smul]
  have hQtr : ∀ (k : KG ε) (v : kfin ε σ), Q (tr k v) = Q v := fun k v => hQ _ (toMK_mem_K _) v _ rfl
  refine ⟨bf hU l, fun k hk v y v' y' hv' hy' => ?_, fun v y => ?_, ?_⟩
  ·
    obtain ⟨k0, rfl⟩ : ∃ k0 : KG ε, toMK k0 = k := by rw [← range_toMK ε] at hk; exact hk
    have htr : ∀ (k : KG ε) (w w' : kfin ε σ), (w' : H) = σ (toMK k0) w → tr k w' = tr (k0⁻¹ * k) w := by
      intro k w w' hw
      apply Subtype.ext
      show σ (toMK k⁻¹) (w' : H) = σ (toMK (k0⁻¹ * k)⁻¹) w
      rw [hw, ← sigma_mul hU (K_le_UJ (toMK_mem_K _)) (K_le_UJ (toMK_mem_K _))]
      congr 2
    rw [bf_apply, bf_apply, fm, fm]
    simp only [htr _ _ _ hv', htr _ _ _ hy']
    exact integral_mul_left_eq_self (fun k => conj (l (tr k v)) * l (tr k y)) k0⁻¹
  · rw [bf_apply, fm]
    have h := norm_integral_le_of_norm_le_const (μ := muK ε) (f := fun k => conj (l (tr k v)) * l (tr k y))
      (C := Q v * Q y) (Filter.Eventually.of_forall fun k => by
        rw [norm_mul, RCLike.norm_conj, ← hQtr k v, ← hQtr k y]
        exact mul_le_mul (hlQ _) (hlQ _) (norm_nonneg _) (apply_nonneg _ _))
    simpa [measure_univ] using h
  · rw [bf_apply, fm]
    haveI : CompactSpace (KG ε) := instCompactKG n ε
    have e : ∀ k : KG ε, conj (l (tr k v₀)) * l (tr k v₀) = ((‖l (tr k v₀)‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [mul_comm, Complex.mul_conj']
      push_cast
      ring
    simp only [e]
    rw [integral_complex_ofReal]
    have hpos : 0 < ∫ k, ‖l (tr k v₀)‖ ^ 2 ∂(muK ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        ((continuous_tr hU l v₀).norm.pow 2) (isClosed_tsupport _).isCompact (fun k => by positivity) ?_
      have h1 : tr (1 : KG ε) v₀ = v₀ := Subtype.ext (by
        show σ (toMK (1 : KG ε)⁻¹) (v₀ : H) = v₀
        rw [inv_one]
        exact sigma_one hU _)
      rw [h1, hlv, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg Q v₀)]
      exact pow_ne_zero 2 hv₀
    exact_mod_cast hpos.ne'

end PositivityTheory.CW

end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum Filter Topology

namespace PositivityTheory.CW

namespace ExistsNormingFunctional

theorem exists_norming {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) (x₀ : E) :
    ∃ φ : Module.Dual ℂ E, ‖φ x₀‖ = q x₀ ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have H : ∀ c : ℂ, c • x₀ = 0 → (RingHom.id ℂ) c • ((q x₀ : ℝ) : ℂ) = 0 := by
    intro c hc
    have h0 : ‖c‖ * q x₀ = 0 := by rw [← map_smul_eq_mul q, hc, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [norm_eq_zero.1 h]
    · simp [h]
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) :=
    (LinearPMap.mkSpanSingleton' x₀ ((q x₀ : ℝ) : ℂ) H).toFun
  have hf : ∀ (c : ℂ) (h : c • x₀ ∈ Submodule.span ℂ {x₀}), f ⟨c • x₀, h⟩ = c * (q x₀ : ℂ) := by
    intro c h
    exact (LinearPMap.mkSpanSingleton'_apply x₀ ((q x₀ : ℝ) : ℂ) H c h).trans (by simp)
  have h1 : f ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ = (q x₀ : ℂ) :=
    LinearPMap.mkSpanSingleton'_apply_self x₀ ((q x₀ : ℝ) : ℂ) H _
  obtain ⟨g, hg, hgq⟩ := Module.Dual.exists_extension_of_le_seminorm
    (Submodule.span ℂ {x₀}) f (p := q) (by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      exact le_of_eq (map_smul_eq_mul q c x₀).symm)
  refine ⟨g, ?_, hgq⟩
  have h2 := hg ⟨x₀, Submodule.mem_span_singleton_self x₀⟩
  rw [h1] at h2
  rw [show g x₀ = (q x₀ : ℂ) from h2, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]

end ExistsNormingFunctional

private theorem exp_smul_mem_UJset_of_mem_lieSet {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ lieSet ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε := by
  set J := ReciprocityTheory.ChartRestriction.DS.Jm ε with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hX' : Xᴴ * J + J * X = 0 := hX
  set Y : Matrix (Fin n) (Fin n) ℂ := t • X with hYdef
  have hYJ : Yᴴ * J = -(J * Y) := by
    rw [hYdef, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, Matrix.mul_smul,
      eq_neg_of_add_eq_zero_left hX', smul_neg]
  have hY : Yᴴ = J * (-Y) * J := by
    calc Yᴴ = Yᴴ * J * J := by rw [mul_assoc, hJJ, mul_one]
      _ = J * (-Y) * J := by rw [hYJ, mul_neg, neg_mul]
  have hexp : NormedSpace.exp Yᴴ = J * NormedSpace.exp (-Y) * J := by
    have h := Matrix.exp_units_conj u (-Y)
    rw [hY]
    exact h
  have hdet : IsUnit (NormedSpace.exp Y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  show (NormedSpace.exp Y)ᴴ * J * NormedSpace.exp Y = J
  rw [← Matrix.exp_conjTranspose, hexp, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc J J, hJJ, one_mul, Matrix.nonsing_inv_mul _ hdet, mul_one]

theorem d1b : D1 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hCore T₀ hT i
  obtain ⟨q, N, hq, hgrow⟩ := hπ.growth i
  obtain ⟨S, C, I₀, hS, hC, hI₀, hmain⟩ := hCore N
  refine ⟨S, C * ∑ e ∈ I₀, q (T₀ e), hS, ?_⟩
  intro w hw
  obtain ⟨φ, hφ1, hφ2⟩ := ExistsNormingFunctional.exists_norming (p i) (T₀ w)
  have hφc : Continuous φ :=
    hπ.withSeminorms.continuous_normedSpace_rng ℂ φ ⟨{i}, 1, by
      intro x
      simpa using hφ2 x⟩
  let F : H →ₗ[ℂ] Mx n → ℂ :=
    LinearMap.pi (fun g => φ ∘ₗ (π g).toLinearMap ∘ₗ T₀)
  have hF : ∀ v g, F v g = φ (π g (T₀ v)) := fun _ _ => rfl
  have hpos : ∀ g : Mx n, 0 ≤ (1 + hs g) ^ N := by
    intro g
    apply pow_nonneg
    have : 0 ≤ hs g := by
      unfold hs
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hB : 0 ≤ ∑ e ∈ I₀, q (T₀ e) := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have key := hmain F
    (fun v _ => by
      show ContinuousOn (fun g => φ (π g (T₀ v))) (UJset ε)
      exact hφc.comp_continuousOn (hπ.continuousOn (T₀ v)))
    (fun X hX v hv g hg => by
      rw [hF, hT.2 X hX v hv, hasDerivAt_iff_tendsto_slope]
      have hΛ : Continuous fun z : E => φ (π g z) := hφc.comp (π g).continuous
      have heq : slope (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) 0 =
          fun t : ℝ => φ (π g (((t : ℂ))⁻¹ • ((π (NormedSpace.exp (t • X))) (T₀ v) - T₀ v))) := by
        funext t
        rw [slope_def_module]
        simp only [hF, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
          hπ.map_mul g hg _ (exp_smul_mem_UJset_of_mem_lieSet ε X hX t), ContinuousLinearMap.comp_apply, map_smul, map_sub,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_inv]
      rw [heq]
      exact (hΛ.tendsto _).comp (hπ.hasDRep X hX (T₀ v)))
    (fun v _ => ⟨q (T₀ v), fun g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ v))‖ ≤ p i (π g (T₀ v)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ v) := hgrow g hg (T₀ v)
        _ = q (T₀ v) * (1 + hs g) ^ N := mul_comm _ _⟩)
    (∑ e ∈ I₀, q (T₀ e)) hB
    (fun e he g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ e))‖ ≤ p i (π g (T₀ e)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ e) := hgrow g hg (T₀ e)
        _ ≤ (1 + hs g) ^ N * ∑ e ∈ I₀, q (T₀ e) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun e => q (T₀ e)) (fun _ _ => apply_nonneg _ _) he)
            (hpos g)
        _ = (∑ e ∈ I₀, q (T₀ e)) * (1 + hs g) ^ N := mul_comm _ _)
    w hw
  rw [hF, hπ.map_one, ContinuousLinearMap.one_apply] at key
  rw [← hφ1]
  exact key

end PositivityTheory.CW
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined

namespace PositivityTheory.CW

namespace ExistsFunctional

theorem exists_functional {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) {x₀ : E} (hx : q x₀ ≠ 0) :
    ∃ φ : Module.Dual ℂ E, φ x₀ ≠ 0 ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have h0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx (map_zero q)
  let e := LinearEquiv.toSpanNonzeroSingleton ℂ E x₀ h0
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) := (q x₀ : ℂ) • (e.symm : _ →ₗ[ℂ] ℂ)
  have hfe : ∀ t : ℂ, f (e t) = t * q x₀ := by
    intro t
    simp [f, mul_comm]
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm (Submodule.span ℂ {x₀}) f
    (p := q) (by
      intro y
      obtain ⟨t, rfl⟩ := e.surjective y
      rw [hfe, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      rw [LinearEquiv.toSpanNonzeroSingleton_apply]
      simp [map_smul_eq_mul])
  refine ⟨g, ?_, hgp⟩
  have h1 := hg (e 1)
  rw [hfe, one_mul] at h1
  have : ((e 1 : Submodule.span ℂ {x₀}) : E) = x₀ := by
    rw [LinearEquiv.toSpanNonzeroSingleton_one]
  rw [this] at h1
  rw [h1]
  exact_mod_cast hx

end ExistsFunctional

theorem e1b : faceMap_comp_succAbove_castSucc := by
  unfold faceMap_comp_succAbove_castSucc AllTgt
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hrep T hT i w₀ hw₀ hp u hu hu0
  by_contra hall
  push_neg at hall
  obtain ⟨φ, hφ0, hφ⟩ := ExistsFunctional.exists_functional (p i) hp
  let ℓ : H →ₗ[ℂ] ℂ := φ ∘ₗ T
  have hlie : ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n))) = lieSet ε := rfl
  have hsm : ∀ w, Sm ε σ w →
      w ∈ GlobalTheory.LowTypeDetermined.smooth (Jm ε) (fun g => σ (1 * g * (1 : Mx n)⁻¹)) := by
    intro w hw
    change SmoothVec ((GlobalTheory.LowTypeDetermined.lie (Jm ε) : Set (Mx n)))
      (fun g => σ (1 * g * (1 : Mx n)⁻¹)) w
    simp only [inv_one, mul_one, one_mul]
    rw [hlie]
    exact hw
  have key := GlobalTheory.LowTypeDetermined.eq_zero_of_translates (G := Jm ε) (P := 1) hU hI isUnit_one
    (by simp) (ℓ := ℓ) ?_ (hsm u hu) hu0 ?_ (hsm w₀ hw₀)
  · exact hφ0 key
  · obtain ⟨S, C, hS, hb⟩ := hT.2 i
    refine ⟨S, C, ?_, ?_⟩
    · rw [hlie]
      exact hS
    · simp only [inv_one, mul_one, one_mul]
      rw [hlie]
      intro w hw
      exact (hφ (T w)).trans (hb w hw)
  · intro g hg
    show φ (T (σ g u)) = 0
    rw [hT.1 g hg u hu]
    exact norm_le_zero_iff.mp ((hφ _).trans (hall g hg).le)

end PositivityTheory.CW
end

section

namespace PositivityTheory.CW

theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
end
