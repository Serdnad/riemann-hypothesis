module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.Etale.Weakly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem dCount : AMem → ABnfH → AOrb → DCount := by
  intro hM hB hO F _ _ _ c hc χ
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hKH : Kc c ≤ Hc c := le_sup_left
  have hzH : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  obtain ⟨-, -, hKK, hHd, -⟩ := hM F
  show Countable (GF F ⧸ Hc c) ∧ ∀ a : GF F,
    {ω : GF F ⧸ Hc c | ∃ h ∈ Hc c, ω = ((h * a : GF F) : GF F ⧸ Hc c)}.Finite
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨S, hS⟩ := hB F c hc
    have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    have : Countable (GL (Fin 2) F) :=
      (show Function.Injective (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) from
        fun _ _ h => Units.ext h).countable
    refine Function.Surjective.countable
      (f := fun p : GL (Fin 2) F × S => ((jF F p.1 * p.2.1 : GF F) : GF F ⧸ Hc c)) ?_
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
      refine ⟨(b⁻¹, ⟨x', hx'⟩), QuotientGroup.eq.2 ?_⟩
      have hx : x = jF F b⁻¹ * x' * h := by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]
      show (jF F b⁻¹ * x')⁻¹ * x ∈ Hc c
      rw [hx, inv_mul_cancel_left]
      exact hKH hh
  · obtain ⟨S, hS⟩ := hO F c hc a
    refine (S.finite_toSet.image (fun x : GF F => (x : GF F ⧸ Hc c))).subset ?_
    rintro ω ⟨h, hh, rfl⟩
    obtain ⟨k, hk, z, rfl⟩ := (hHd c h).1 hh
    obtain ⟨x', hx', h', hh', e⟩ := hS k (hKK c hk)
    refine ⟨x', hx', QuotientGroup.eq.2 ?_⟩
    have he : k * zc F z * a = x' * (h' * zc F z) := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zc_center z) a, ← mul_assoc, e, mul_assoc]
    rw [he, inv_mul_cancel_left]
    exact mul_mem (hKH hh') (hzH z)

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

variable {F : Type} [Field F]

namespace UpperTheory.Esk.MinkowskiHeightLemmas

private theorem term (σ : F →+* ℝ) (γ : GL (Fin 2) F) (s : Fin 2 → F) (z : P) :
    |(Matrix.GeneralLinearGroup.map σ γ • z).1.im| /
      ‖(σ (s 0) : ℂ) * (Matrix.GeneralLinearGroup.map σ γ • z).1 + (σ (s 1) : ℂ)‖ ^ 2 =
    |σ γ.val.det| * (|z.1.im| / ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
  set g := Matrix.GeneralLinearGroup.map σ γ
  have hd : den g z.1 ≠ 0 := den_ne g z.2
  have hdet : g.val.det = σ γ.val.det := by
    rw [det_eq, Matrix.det_fin_two]; simp [g]
  have e : (σ (s 0) : ℂ) * (g • z).1 + (σ (s 1) : ℂ) =
      ((σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)) / den g z.1 := by
    rw [coe_smul, eq_div_iff hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    simp [g, num, den, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [e, coe_smul, im_div, hdet, norm_div, div_pow, Complex.normSq_eq_norm_sq, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg ‖den g z.1‖)]
  have hn : ‖den g z.1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hd)
  by_cases h0 : ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2 = 0
  · rw [h0]; simp
  · field_simp

private theorem ht_act {I Gf : Type} [Group Gf] [Fintype I] (D : Dat F I Gf) (s : Fin 2 → F) (γ : GL (Fin 2) F)
    (z : X I) (x : Gf) (hrat : D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x) :
    D.Ht (s ᵥ* γ.val) z x = D.Ht s (D.act γ z) (D.j γ * x) := by
  simp only [Dat.Ht, Dat.act, Dat.r, term, Finset.prod_mul_distrib, ← hrat]
  ring

private theorem row_ne {σ : F →+* ℝ} {s : Fin 2 → F} (hs : s ≠ 0) {w : ℂ} (hw : w.im ≠ 0) :
    (σ (s 0) : ℂ) * w + (σ (s 1) : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  simp [hw] at h1
  rw [h1] at h
  simp at h
  exact hs (funext fun i => by fin_cases i <;> simp [h1, h])

private theorem arch_le {σ : F →+* ℝ} {N : ℕ} (hN : N ≠ 0) {C : ℝ} (hC : 0 < C) {s : Fin 2 → F} (hs : s ≠ 0)
    {w : ℂ} (hw : w.im ≠ 0) (hb : ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 ≤ C * |w.im|) :
    1 / ((N : ℝ) ^ 2 * C) ≤ |w.im| / ‖(σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ)‖ ^ 2 := by
  have e : (σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ) = (N : ℂ) * ((σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)) := by
    simp [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
  have hY := row_ne (σ := σ) hs hw
  have hY2 : 0 < ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 := by positivity
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [e, norm_mul, mul_pow, Complex.norm_natCast, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hb hN2.le]

private theorem fin_min {α : Type} (S : Finset α) (f : α → ℝ) (hf : ∀ a, 0 < f a) : ∃ c : ℝ, 0 < c ∧ ∀ a ∈ S, c ≤ f a := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, -, ha⟩ := S.exists_min_image f hS
    exact ⟨f a, hf a, ha⟩
  · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hS⟩

private theorem nF_le (hMem : AMem) (hMono : AMono) (hRow : ARow) [NumberField F] {x : GF F} {N : ℕ}
    (hNx : ∀ i j, (N : Af F) * x.val i j ∈ Ohat F) {s0 : Fin 2 → F} (hint : ∀ i, IsIntegral ℤ (s0 i))
    (hs : (N : F) • s0 ≠ 0) : nF ((N : F) • s0) x ≤ 1 := by
  obtain ⟨t, k, hk, hrow⟩ := (hRow F ((N : F) • s0) x).1 hs
  rw [(hRow F _ x).2 t k hk hrow]
  have hM := hMem F
  have hmem : ∀ i, rowF ((N : F) • s0) x i ∈ Ohat F := fun i => by
    simp only [rowF, Matrix.vecMul, dotProduct]
    refine Subring.sum_mem _ fun j _ => ?_
    have e : algebraMap F (Af F) (((N : F) • s0) j) * x.val j i = algebraMap F (Af F) (s0 j) * ((N : Af F) * x.val j i) := by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
    rw [e]
    exact Subring.mul_mem _ ((hM.2.2.2.2.2.1 (s0 j)).1 (hint j)) (hNx j i)
  calc absF t ≤ absF 1 := hMono F t 1 (fun w => by
        have hv : ∀ i, Valued.v (pLoc F w (rowF ((N : F) • s0) x i)) ≤ 1 := fun i => (hM.2.1 _).1 (hmem i) w
        obtain ⟨-, hmax⟩ := hM.2.2.2.2.1 k hk w
        rw [Units.val_one, map_one, map_one]
        rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h <;> rw [h] at hmax
        · have := hv 0
          rwa [hrow 0, map_mul, map_mul, hmax, mul_one] at this
        · have := hv 1
          rwa [hrow 1, map_mul, map_mul, hmax, mul_one] at this)
    _ = 1 := by simp [absF]

private theorem exists_height_lower_bound (hMem : AMem) (hMono : AMono) (hRow : ARow) (hMink : AMink) (hHt : DHt) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (c : Pl F → ℕ) (hc : {w | c w ≠ 0}.Finite) (χ : Hc c →* ℂˣ) (x : GF F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : X (InfinitePlace F), ∃ s, s ≠ 0 ∧ c₀ ≤ (mkDat c χ).Ht s z x := by
  obtain ⟨C, hC, hmink⟩ := hMink F
  obtain ⟨N, hN, hNx⟩ := (hMem F).2.2.2.2.2.2.1 x
  have hpos : ∀ s : Fin 2 → F, s ≠ 0 → 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 :=
    fun s hs => (hHt F c hc χ).1 s hs x
  have ha : 0 < absF (Matrix.GeneralLinearGroup.det x) := by
    by_contra h
    replace h := not_lt.1 h
    exact (hpos ![1, 0] (by intro h; simpa using congrFun h 0)).not_ge (div_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))
  refine ⟨absF (Matrix.GeneralLinearGroup.det x) * (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F), by positivity,
    fun z => ?_⟩
  obtain ⟨s0, hs0, hint, hb⟩ := hmink (fun v => (z v).1) (fun v => (z v).2)
  have hs : (N : F) • s0 ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.2 hN) hs0
  refine ⟨_, hs, ?_⟩
  have hn := nF_le hMem hMono hRow hNx hint hs
  have hn0 : 0 ≤ nF ((N : F) • s0) x := finprod_nonneg fun w => (norm_nonneg _).trans (le_max_left _ _)
  have hp := hpos _ hs
  have hfin : absF (Matrix.GeneralLinearGroup.det x) ≤ absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2 := by
    have h2 : 0 < nF ((N : F) • s0) x ^ 2 := by
      rcases (pow_nonneg hn0 2).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hp; exact absurd hp (lt_irrefl 0)
    rw [le_div_iff₀ h2]
    nlinarith [pow_le_one₀ hn0 hn (n := 2)]
  have harch : (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F) ≤ ∏ v, |(z v).1.im| /
      ‖((mkDat c χ).σ v (((N : F) • s0) 0) : ℂ) * (z v).1 + ((mkDat c χ).σ v (((N : F) • s0) 1) : ℂ)‖ ^ 2 := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun v _ => arch_le hN hC hs0 (z v).2 (hb v)
  have hm := mul_le_mul harch hfin ha.le (Finset.prod_nonneg fun _ _ => by positivity)
  unfold Dat.Ht
  change _ ≤ _ * (absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2)
  linarith

end UpperTheory.Esk.MinkowskiHeightLemmas

open UpperTheory.Esk.MinkowskiHeightLemmas in
theorem UpperTheory.Esk.dMink : UpperTheory.Esk.AMem → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.ABnfH → UpperTheory.Esk.AMink → UpperTheory.Esk.DHt → UpperTheory.Esk.DMul → UpperTheory.Esk.DMink := by
  intro hMem hMono hRow hBnfH hMink hHt hMul F _ _ _ c hc χ
  obtain ⟨S, hS⟩ := hBnfH F c hc
  choose cf hcf hcz using fun x => exists_height_lower_bound hMem hMono hRow hMink hHt F c hc χ x
  obtain ⟨c₀, hc₀, hle⟩ := fin_min S cf hcf
  refine ⟨c₀, hc₀, fun z x => ?_⟩
  obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
  obtain ⟨s', hs', hs'le⟩ := hcz x' ((mkDat c χ).act b z)
  refine ⟨s' ᵥ* b.val, ?_, ?_⟩
  · intro h0
    apply hs'
    have := congrArg (· ᵥ* (b⁻¹ : GL (Fin 2) F).val) h0
    simpa [Matrix.vecMul_vecMul] using this
  · rw [ht_act _ _ _ _ _ ((hHt F c hc χ).2.1 s' hs' b x)]
    have ej : (mkDat c χ).j b * x = x' * h := e
    have hH : h ∈ (mkDat c χ).H := Subgroup.mem_sup_left hh
    have hl := (hMul F c hc χ).1 s' hs' x' h hH
    rw [ej]
    unfold Dat.Ht at hs'le ⊢
    rw [hl]
    exact (hle x' hx').trans hs'le
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.PrimitiveVectorLemmas

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_row (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL (Fin 2) F, ∀ j, γ.val 1 j = s j := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1; apply hs; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro j; fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro j; fin_cases j <;> rfl

theorem row_mul (s : Fin 2 → F) (γ : GL (Fin 2) F) (hγ : ∀ j, γ.val 1 j = s j) (x : GF F) (i : Fin 2) :
    rowF s x i = (jF F γ * x).val 1 i := by
  simp [rowF, jF, Matrix.mul_apply, Matrix.vecMul, dotProduct, hγ]

theorem row_zak (d a : (Af F)ˣ) (u : Af F) (k : GF F) (i : Fin 2) :
    (zc F d * aff a u * k).val 1 i = (d : Af F) * k.val 1 i := by
  simp [zc, aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]

end UpperTheory.Esk.PrimitiveVectorLemmas

theorem UpperTheory.Esk.aRow : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ARow := by
  intro hM hI F _ _ s x
  refine ⟨fun hs => ?_, fun t k hk hrow => ?_⟩
  · obtain ⟨γ, hγ⟩ := UpperTheory.Esk.PrimitiveVectorLemmas.exists_row s hs
    obtain ⟨d, a, u, k, hk, he⟩ := hI F (UpperTheory.Esk.jF F γ * x)
    refine ⟨d, k, hk, fun i => ?_⟩
    rw [UpperTheory.Esk.PrimitiveVectorLemmas.row_mul s γ hγ x i, he, UpperTheory.Esk.PrimitiveVectorLemmas.row_zak]
  · obtain ⟨-, -, -, -, h5, -⟩ := hM F
    have key : ∀ w : Pl F, max ‖pLoc F w (k.val 1 0)‖ ‖pLoc F w (k.val 1 1)‖ = 1 := by
      intro w
      have h := (h5 k hk w).2
      refine le_antisymm (max_le (Valued.toNormedField.norm_le_one_iff.2 ((le_max_left _ _).trans h.le))
        (Valued.toNormedField.norm_le_one_iff.2 ((le_max_right _ _).trans h.le))) ?_
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with hh | hh <;> rw [hh] at h
      · exact le_max_of_le_left (Valued.toNormedField.one_le_norm_iff.2 h.ge)
      · exact le_max_of_le_right (Valued.toNormedField.one_le_norm_iff.2 h.ge)
    have hw : ∀ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ =
        ‖pLoc F w (t : Af F)‖ := by
      intro w
      rw [hrow 0, hrow 1, map_mul, map_mul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _), key w, mul_one]
    show ∏ᶠ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ = ∏ᶠ w : Pl F, ‖pLoc F w (t : Af F)‖
    exact finprod_congr hw
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace UnipotentNormalization

def up {F : Type} [Field F] (u t : F) (hu : u ≠ 0) : GL (Fin 2) F :=
  ⟨!![u, t; 0, 1], !![u⁻¹, -t * u⁻¹; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring⟩

theorem up_mem (hM : AMem) {F : Type} [Field F] [NumberField F] (u t : F) (hu : u ≠ 0)
    (h1 : IsIntegral ℤ u) (h2 : IsIntegral ℤ u⁻¹) (h3 : IsIntegral ℤ t) : jF F (up u t hu) ∈ K0 F := by
  have hI : ∀ g : GL (Fin 2) F, (∀ i j, IsIntegral ℤ (g.val i j)) → ∀ i j, (jF F g).val i j ∈ Ohat F := by
    intro g hg i j
    change algebraMap F (Af F) (g.val i j) ∈ Ohat F
    exact ((hM F).2.2.2.2.2.1 _).1 (hg i j)
  refine ((hM F).1 _).2 ⟨hI _ ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [up, h1, h3, isIntegral_zero, isIntegral_one]
  · rw [← map_inv]
    refine hI _ ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp [up, h2, isIntegral_zero, isIntegral_one, h3.mul h2]

theorem ht01 {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem ht_inv {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (h2 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x)
    (h3 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2)
    (b : GL (Fin 2) F) (hb : b 1 0 = 0) (z : X I) (x : Gf) :
    D.Ht ![0, 1] (D.act b z) (D.j b * x) = D.Ht ![0, 1] z x := by
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have hdb : b.val.det = b 0 0 * b 1 1 := by
    rw [Matrix.det_fin_two]; simp [hb]
  have hdet : b.val.det ≠ 0 := b.det_ne_zero
  have hd : b 1 1 ≠ 0 := fun e => hdet (by rw [hdb, e, mul_zero])
  have hv : (![0, 1] : Fin 2 → F) ᵥ* b.val = b 1 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  have key := h2 _ hs b x
  rw [hv, h3 _ hs _ hd] at key
  have him : ∀ v, ((D.act b z v).1).im = D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im := by
    intro v
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    simp only [Dat.act, coe_smul]
    rw [im_div, det_eq]
    simp [den, Dat.r, hb, Complex.normSq_ofReal]
    field_simp
  rw [ht01, ht01]
  simp_rw [him]
  have hpd : ∏ v, |D.σ v b.val.det| ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => abs_ne_zero.2 ((map_ne_zero _).2 hdet)
  apply mul_right_cancel₀ hpd
  have e : (∏ v, |D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im|) * ∏ v, D.σ v (b 1 1) ^ 2 =
      (∏ v, |(z v).1.im|) * ∏ v, |D.σ v b.val.det| := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    rw [hdb, map_mul, abs_mul, abs_mul, abs_div, ← sq_abs (D.σ v (b 1 1))]
    have : |D.σ v (b 1 1)| ≠ 0 := abs_ne_zero.2 hσ
    field_simp
  rw [mul_assoc, key]
  linear_combination D.hf ![0, 1] x * e

theorem act_up {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (χ : Hc c →* ℂˣ)
    (u t : F) (hu : u ≠ 0) (z : X (InfinitePlace F)) (v : InfinitePlace F) :
    (((mkDat c χ).act (up u t hu) z) v).1 = (sg v u : ℂ) * (z v).1 + (sg v t : ℂ) := by
  simp [Dat.act, coe_smul, num, den, Dat.r, up, mkDat]

theorem low {ι : Type} [Fintype ι] (y : ι → ℝ) {C c₀ M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hy : ∀ v v', |y v| ≤ C * |y v'|) (h : c₀ ≤ (∏ v, |y v|) * M) (v : ι) : min 1 (c₀ / M) / C ≤ |y v| := by
  rw [div_le_iff₀ hC, mul_comm]
  have ha : 0 ≤ C * |y v| := by positivity
  rcases le_or_gt 1 (C * |y v|) with h1 | h1
  · exact (min_le_left _ _).trans h1
  · have : Nonempty ι := ⟨v⟩
    have hp : ∏ v', |y v'| ≤ (C * |y v|) ^ Fintype.card ι := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun v' _ => hy v' v
    have hpow := pow_le_of_le_one ha h1.le (Fintype.card_ne_zero (α := ι))
    have hcm : c₀ / M ≤ C * |y v| := by
      rw [div_le_iff₀ hM]
      exact h.trans (mul_le_mul_of_nonneg_right (hp.trans hpow) hM.le)
    exact (min_le_right _ _).trans hcm

end UnipotentNormalization

open UnipotentNormalization in
theorem dNormal : AMem → ABnfH → AOrb → AUnit → ATrans → DHt → DMul → DNormal := by
  intro hM hB hO hU hT hH hMu F _ _ _ c hc χ c₀ hc₀
  classical
  obtain ⟨S0, hS0⟩ := hB F c hc
  choose S' hS' using fun x1 : GF F => hO F c hc x1
  obtain ⟨CU, hCU, hU'⟩ := hU F
  obtain ⟨CT, hCT, hT'⟩ := hT F
  obtain ⟨-, h2, h3⟩ := hH F c hc χ
  obtain ⟨hm, -⟩ := hMu F c hc χ
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  set S := S0.biUnion S' with hSdef
  set M : ℝ := 1 + ∑ x' ∈ S, |(mkDat c χ).hf ![0, 1] x'| with hMdef
  have hM0 : 0 < M := by positivity
  have hMS : ∀ x' ∈ S, (mkDat c χ).hf ![0, 1] x' ≤ M := fun x' hx' =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun x' => |(mkDat c χ).hf ![0, 1] x'|)
      (fun _ _ => abs_nonneg _) hx').trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨S, max CU CT, min 1 (c₀ / M) / CU, by positivity, fun z x hz => ?_⟩
  obtain ⟨b1, hb1, x1, hx1, h1, hh1, e1⟩ := hS0 x
  obtain ⟨u, hu0, hui, hui', hu⟩ := hU' (fun v => (((mkDat c χ).act b1 z) v).1.im) (fun v => (((mkDat c χ).act b1 z) v).2)
  obtain ⟨t, hti, ht⟩ := hT' (fun v => sg v u * (((mkDat c χ).act b1 z) v).1.re)
  obtain ⟨x', hx', h2', hh2, e2⟩ := hS' x1 _ (up_mem hM u t hu0 hui hui' hti)
  have hb : (up u t hu0 * b1) 1 0 = 0 := by
    simp [up, Matrix.mul_apply, Fin.sum_univ_two, hb1]
  have hact : (mkDat c χ).act (up u t hu0 * b1) z = (mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z) := by
    funext v; simp only [Dat.act, map_mul, mul_smul]
  have hj : (mkDat c χ).j (up u t hu0 * b1) * x = x' * (h2' * h1) := by
    change jF F (up u t hu0 * b1) * x = _
    rw [map_mul, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  have hH' : h2' * h1 ∈ (mkDat c χ).H := Subgroup.mem_sup_left (mul_mem hh2 hh1)
  have hx'S : x' ∈ S := Finset.mem_biUnion.2 ⟨x1, hx1, hx'⟩
  refine ⟨up u t hu0 * b1, hb, ⟨x', hx'S, h2' * h1, hH', hj⟩, ?_⟩
  have e := ht_inv (mkDat c χ) h2 h3 _ hb z x
  rw [← e, hj, hact, ht01, hm _ hs _ _ hH'] at hz
  rw [hact]
  have hre : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.re =
      sg v u * (((mkDat c χ).act b1 z) v).1.re + sg v t := by
    intro v; rw [act_up]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im =
      sg v u * (((mkDat c χ).act b1 z) v).1.im := by
    intro v; rw [act_up]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hy : ∀ v v', |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im| ≤
      CU * |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v').1.im| := by
    intro v v'; rw [him, him]; exact hu v v'
  have hprod : c₀ ≤ (∏ v, |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im|) * M :=
    hz.trans (mul_le_mul_of_nonneg_left (hMS x' hx'S) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
  intro v
  refine ⟨?_, low _ hCU hM0 hy hprod v, fun v' => ?_⟩
  · rw [hre]; exact (ht v).trans (le_max_right _ _)
  · exact (hy v v').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end UpperTheory.Esk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aBnfH : UpperTheory.Esk.ABnf → UpperTheory.Esk.AOrb → UpperTheory.Esk.ABnfH := by
  classical
  intro hB hO F _ _ c hc
  obtain ⟨S, hS⟩ := hB F
  obtain ⟨T, hT⟩ := hO F c hc 1
  refine ⟨Finset.image₂ (· * ·) S T, fun x => ?_⟩
  obtain ⟨b, hb, x', hx', k, hk, hx⟩ := hS x
  obtain ⟨y, hy, h, hh, hkh⟩ := hT k hk
  refine ⟨b, hb, x' * y, Finset.mem_image₂_of_mem hx' hy, h, hh, ?_⟩
  rw [hx, mul_assoc, ← hkh, mul_one]

end UpperTheory.Esk
end
end
