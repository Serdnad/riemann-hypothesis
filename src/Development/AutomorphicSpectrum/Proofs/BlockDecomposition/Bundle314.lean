module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle238
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle298
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem locCpt (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_haar (n : ℕ) : ∃ (_ : MeasurableSpace (G n)) (_ : BorelSpace (G n)) (μ : Measure (G n)), μ.IsHaarMeasure := by
  haveI := locCpt n
  letI : MeasurableSpace (G n) := borel _
  haveI : BorelSpace (G n) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, Measure.haar, inferInstance⟩

theorem waveEq {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (A : E.V →L[ℂ] E.V)
    (hA : ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g)) :
    ∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + (A.restrictScalars ℝ) (u s y) := by
  intro s y hy
  have h := hu.2.2.1 s y hy
  rw [hA _ (hu.2.1 s) y hy] at h
  have h2 : dt (dt u) s y = iteratedDeriv 2 (fun r => u r y) s := by
    simp only [dt, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h2, h]
  have : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  rfl

theorem speed_pos (hL : LgFacts) (hR : RCalc) {n : ℕ} (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hlg : ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C₁)
    (χ : ℝ → ℝ) (h1 : ContDiff ℝ ∞ χ) (h2 : ∀ x, deriv χ x ≤ 0) (h3 : ∀ x, 0 ≤ χ x) (h4 : ∀ x, x ≤ 0 → χ x = 1) (h5 : ∀ x, 1 ≤ x → χ x = 0)
    (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (t : ℝ) (ht : 0 ≤ t) (x : Mat n) (hx : x ∈ GLs n)
    (C : ℝ) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (h0 : ∀ y ∈ GLs n, lg y ≤ lg (1 : Mat n) + 1 + C * t → u 0 (x * y) = 0) : u t x = 0 := by
  obtain ⟨mG, bG, μ, hμ⟩ := exists_haar n
  letI : InnerProductSpace ℝ E.V := InnerProductSpace.rclikeToReal ℂ E.V
  obtain ⟨A, hA⟩ := GlobalTheory.T.casimir_right_laplacian_formula E
  obtain ⟨l1, l2, l3⟩ := hlg x hx
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hxx : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul _ hxu
  have hxx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
  have hxi : x⁻¹ ∈ GLs n := by
    have : x⁻¹.det * x.det = 1 := by rw [← Matrix.det_mul, hxx, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this |> fun h => h
  have hmul : ∀ y ∈ GLs n, x⁻¹ * y ∈ GLs n := fun y hy => by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul]
    exact mul_ne_zero hxi hy
  have hbp : ∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg (x⁻¹ * y) → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
    intro Ψ hΨ ⟨R, hRΨ⟩ X
    refine GlobalTheory.T.integral_right_derivative_zero_alt hR μ Ψ hΨ ⟨R + lg x, fun y hy hlt => hRΨ y hy ?_⟩ X
    have := (hL n).1 x hx _ (hmul y hy)
    rw [← mul_assoc, hxx', one_mul] at this
    linarith
  have hv := GlobalTheory.T.energy_identity_of_length_function (W := E.V) μ (fun y => lg (x⁻¹ * y)) l1 l2 C₁ hC₁ l3 hbp χ h1 h2 h3 h5 u hu.1
    (A.restrictScalars ℝ) (waveEq E u hu A hA) C hC (lg (1 : Mat n) + C * t) h4 ?_ ?_ t ht x hx ?_
  · exact hv
  · intro y hy hlt
    have := h0 (x⁻¹ * y) (hmul y hy) (by have h' : lg (x⁻¹ * y) < lg (1 : Mat n) + C * t + 1 := hlt; linarith)
    rwa [← mul_assoc, hxx', one_mul] at this
  · intro y hy
    exact hu.2.2.2 y hy
  · simp only [hxx]
    exact le_refl _

theorem asmSpeed : AsmSpeed := by
  intro hL hU hR n
  obtain ⟨C₁, hC₁, hlg⟩ := GlobalTheory.T.translated_length_bounded_derivative hL n
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.smooth_monotone_cutoff_exists
  set C := C₁ * (1 + Fintype.card (Ix n)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hl0 : 0 ≤ lg (1 : Mat n) := by
    unfold lg
    apply Real.log_nonneg
    have : 0 ≤ ∑ a, ∑ b, (‖(1 : Mat n) a b‖ ^ 2 + ‖(1 : Mat n)⁻¹ a b‖ ^ 2) := by positivity
    linarith
  refine ⟨C + lg (1 : Mat n) + 1, ?_⟩
  have key : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ (C + lg (1 : Mat n) + 1) * (1 + t) → u 0 (x * y) = 0) → u t x = 0 := by
    intro E u hu t ht x hx h0
    refine speed_pos hL hR C₁ hC₁ hlg χ h1 h2 h3 h4 h5 E u hu t ht x hx C le_rfl ?_
    intro y hy hle
    refine h0 y hy (hle.trans ?_)
    nlinarith [mul_nonneg hC0 ht, mul_nonneg hl0 ht]
  intro E u hu t x hx h0
  rcases le_total 0 t with ht | ht
  · exact key E u hu t ht x hx (by rwa [abs_of_nonneg ht] at h0)
  · have := key E _ (GlobalTheory.T.wave_time_reversal E u hu) (-t) (by linarith) x hx (by
      intro y hy hle
      simp only [neg_zero]
      exact h0 y hy (by rwa [abs_of_nonpos ht]))
    simpa using this

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LowerOpen

theorem inv_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (x : GL (Fin N) k)
    (p q : Fin N) :
    (((GroundTheory.Automorphic.permGL k w)⁻¹ * x * GroundTheory.Automorphic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h1 : (((GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      w.permMatrix k := by
    rw [← map_inv]
    show ((w⁻¹)⁻¹).permMatrix k = w.permMatrix k
    rw [inv_inv]
  have h2 : ((GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (w⁻¹).permMatrix k := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd q) < blk (stdBlocks d hd) (wOpen d hd p)) : p < q := by
  by_contra hpq
  have h1 := Tuple.monotone_sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) (not_lt.mp hpq)
  simp only [Function.comp_apply, GlobalTheory.CompanionTheory.Rodier.wKey] at h1
  have hb' : blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) q) <
      blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) p) := hb
  rw [Prod.Lex.toLex_le_toLex] at h1
  rcases h1 with h | ⟨h, -⟩
  · exact lt_asymm hb' (OrderDual.toDual_lt_toDual.mp h)
  · exact (ne_of_lt hb') (OrderDual.toDual.injective h)

theorem lower_entries {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) :
    (blk (stdBlocks d hd) i < blk (stdBlocks d hd) j → (x : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (blk (stdBlocks d hd) i = blk (stdBlocks d hd) j →
        (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) := by
  obtain ⟨hpl, hdiag⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).mp hx
  rw [GlobalTheory.SmGL.mem_parabLower_iff] at hpl
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  refine ⟨fun hab => hpl a b i' j' hab, fun hab => ?_⟩
  subst hab
  rw [hdiag a i' j', Matrix.one_apply, Matrix.one_apply]
  simp [(stdBlocks d hd).apply_eq_iff_eq]

theorem parab_inf_lower {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hp : x ∈ parab k (stdBlocks d hd))
    (hx : x ∈ unipRadLower k (stdBlocks d hd)) : x = 1 := by
  ext i j
  rcases lt_trichotomy (blk (stdBlocks d hd) i) (blk (stdBlocks d hd) j) with hlt | heq | hgt
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [(lower_entries hx i j).1 hlt]
    simp [Matrix.one_apply, hij]
  · rw [(lower_entries hx i j).2 heq]
    simp
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hgt
    rw [GlobalTheory.SmGL.mem_parab.mp hp i j hgt]
    simp [Matrix.one_apply, hij]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)


variable {k d hd} in
theorem mem_unipU_iff {u : GL (Fin N) k} :
    u ∈ unipU k d hd ↔ u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  rw [GlobalTheory.CompanionTheory.Rodier.unipU, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem inv_conj_mem_unipU {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd := by
  rw [mem_unipU_iff]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.SmGL.mem_unipB]
    have hent : ∀ p q, (((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (wOpen d hd p) (wOpen d hd q) :=
      fun p q => inv_conj_apply (wOpen d hd) x p q
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hent]
      rcases lt_trichotomy (blk (stdBlocks d hd) (wOpen d hd i)) (blk (stdBlocks d hd) (wOpen d hd j))
        with hlt | heq | hgt
      · exact (lower_entries hx _ _).1 hlt
      · rw [(lower_entries hx _ _).2 heq, Matrix.one_apply, if_neg]
        intro h
        exact hji.ne' ((wOpen d hd).injective h)
      · exact absurd (lt_of_blk_lt d hd hgt) (not_lt.mpr hji.le)
    · rw [hent, (lower_entries hx _ _).2 rfl]
      simp
  · have he : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = x := by group
    rw [he]
    exact hx

theorem eq_of_mul_eq {p u u' : GL (Fin N) k} (hp : p ∈ parab k (stdBlocks d hd))
    (hu : u ∈ unipU k d hd) (hu' : u' ∈ unipU k d hd)
    (e : p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u') : u = u' := by
  have hv : u' * u⁻¹ ∈ unipU k d hd := (unipU k d hd).mul_mem hu' ((unipU k d hd).inv_mem hu)
  have hlow := (mem_unipU_iff.mp hv).2
  have hpeq : pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹ = p := by
    calc pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹
        = (pm k (wOpen d hd) * u') * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by group
      _ = (p * pm k (wOpen d hd) * u) * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by rw [e]
      _ = p := by group
  rw [hpeq] at hlow
  have h1 := parab_inf_lower hp hlow
  rw [h1] at e
  simpa using e

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  have hent : ∀ (i j : Fin N) (c : k),
      IsClosed {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = c} :=
    fun i j c => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hB : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    have hs : (unipB k (Fin N) : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
          ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipB]
    rw [hs]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => hent i j 0).inter
      (isClosed_iInter fun i => hent i i 1)
  have hL : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    have hs : (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) =
        (⋂ a, ⋂ b, ⋂ i, ⋂ j, ⋂ (_ : a < b), {g : GL (Fin N) k |
          (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨b, j⟩) = 0}) ∩
          ⋂ a, ⋂ i, ⋂ j, {g : GL (Fin N) k |
            (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
              (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipRadLower, GlobalTheory.SmGL.mem_parabLower_iff]
    rw [hs]
    exact (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => hent _ _ _).inter
      (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => hent _ _ _)
  have hc : Continuous fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hs : (unipU k d hd : Set (GL (Fin N) k)) =
      (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        (fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    exact mem_unipU_iff
  rw [hs]
  exact hB.inter (hL.preimage hc)

end GlobalTheory.CompanionTheory.Rodier.LowerOpen

namespace GlobalTheory.CompanionTheory.Rodier

theorem unipU_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun x hx => LowerOpen.inv_conj_mem_unipU k d hd hx,
    fun p hp u hu u' hu' e => LowerOpen.eq_of_mul_eq k d hd hp hu hu' e,
    LowerOpen.isClosed_unipU k d hd⟩

end GlobalTheory.CompanionTheory.Rodier
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem antitone_comp_of_adjacent {h N : ℕ} (b : Fin N → Fin h) (w : Equiv.Perm (Fin N))
    (hstep : ∀ i j : Fin N, (j : ℕ) = i + 1 → b (w j) ≤ b (w i)) :
    Antitone (b ∘ w) := by
  intro x y hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only [Fin.mk_le_mk] at hxy
  revert hy
  induction y, hxy using Nat.le_induction with
  | base => intro hy; exact le_rfl
  | succ n hxn ih =>
    intro hy
    have hn : n < N := by omega
    exact le_trans (hstep ⟨n, hn⟩ ⟨n + 1, hy⟩ rfl) (ih hn)

theorem blk_comp_wOpen_antitone {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) :
    Antitone (blk (stdBlocks d hd) ∘ wOpen d hd) := by
  intro x y hxy
  have hm := Tuple.monotone_sort (wKey d hd) hxy
  simp only [Function.comp, wKey] at hm
  rcases Prod.Lex.toLex_le_toLex.mp hm with h | ⟨h, -⟩
  · exact (OrderDual.toDual_lt_toDual.mp h).le
  · exact le_of_eq (OrderDual.toDual_inj.mp h).symm

theorem pm_mem_parab_of_blk_eq (k : Type) [Field k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (v : Equiv.Perm (Fin N)) (hv : ∀ q, blk (stdBlocks d hd) (v q) = blk (stdBlocks d hd) q) :
    pm k v ∈ parab k (stdBlocks d hd) := by
  show (↑(pm k v) : Matrix (Fin N) (Fin N) k).BlockTriangular (blk (stdBlocks d hd))
  intro i j hij
  have hne : v⁻¹ i ≠ j := by
    intro hj
    subst hj
    have hb := hv (v⁻¹ i)
    have hvi : v (v⁻¹ i) = i := by simp
    rw [hvi] at hb
    rw [← hb] at hij
    exact lt_irrefl _ hij
  change (Equiv.toPEquiv v⁻¹).toMatrix i j = 0
  rw [PEquiv.toMatrix_apply]
  simpa using hne

theorem cell_eq_of_blk_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (w w' : Equiv.Perm (Fin N))
    (hw : ∀ p, blk (stdBlocks d hd) (w p) = blk (stdBlocks d hd) (w' p)) :
    cell k d hd w = cell k d hd w' := by
  have key : ∀ u u' : Equiv.Perm (Fin N),
      (∀ p, blk (stdBlocks d hd) (u p) = blk (stdBlocks d hd) (u' p)) → cell k d hd u ⊆ cell k d hd u' := by
    intro u u' hu g hg
    simp only [cell, Set.mem_ofPred_eq] at hg ⊢
    obtain ⟨p, hp, n, hn, rfl⟩ := hg
    have hv : ∀ q, blk (stdBlocks d hd) ((u * u'⁻¹) q) = blk (stdBlocks d hd) q := by
      intro q
      rw [Equiv.Perm.mul_apply, hu]
      simp
    have hpm : pm k u = pm k (u * u'⁻¹) * pm k u' := by
      unfold pm
      rw [← map_mul, inv_mul_cancel_right]
    refine ⟨p * pm k (u * u'⁻¹), (parab k (stdBlocks d hd)).mul_mem hp (pm_mem_parab_of_blk_eq k d hd _ hv),
      n, hn, ?_⟩
    rw [hpm]
    simp only [mul_assoc]
  exact Set.Subset.antisymm (key w w' hw) (key w' w fun p => (hw p).symm)

theorem exists_adjacent_blk_lt_or_cell_eq_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Equiv.Perm (Fin N)),
    (∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)) ∨
      cell k d hd w = cell k d hd (wOpen d hd) := by
  intro k _ _ _ _ h N d hd w
  by_cases hex : ∃ i j : Fin N, (j : ℕ) = i + 1 ∧ blk (stdBlocks d hd) (w i) < blk (stdBlocks d hd) (w j)
  · exact Or.inl hex
  · right
    simp only [not_exists, not_and, not_lt] at hex
    have hA := antitone_comp_of_adjacent (blk (stdBlocks d hd)) w hex
    have hB := blk_comp_wOpen_antitone d hd
    have hU := Tuple.unique_monotone (f := fun q => OrderDual.toDual (blk (stdBlocks d hd) q))
      (σ := w) (τ := wOpen d hd) (monotone_toDual_comp_iff.mpr hA) (monotone_toDual_comp_iff.mpr hB)
    refine cell_eq_of_blk_eq k d hd w (wOpen d hd) fun p => ?_
    exact OrderDual.toDual_inj.mp (congrFun hU p)

end GlobalTheory.CompanionTheory.Rodier
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def whitFirstLin (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : X 0 →ₗ[ℂ] (PiTensorProduct ℂ X ⧸ whitKer ψ d (piTensor ρ)) :=
  (whitKer ψ d (piTensor ρ)).mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v 0

theorem whitFirstLin_apply (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) (x : X 0) :
    whitFirstLin ψ d ρ v x = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ (Function.update v 0 x)) := rfl

def whitFirstMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Fin 2 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (v : ∀ a, X a) : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)) :=
  .mk (whitFirstLin ψ d ρ v) (fun g => by
    ext x
    have h : ∀ a, Function.update v 0 (ρ 0 g x) a = ρ a (firstEmb d g a) (Function.update v 0 x a) :=
      Fin.forall_fin_two.2 ⟨by simp [firstEmb], by simp [firstEmb]⟩
    simp only [LinearMap.comp_apply, whitFirstLin_apply, whit2_mk, piTensor_tprod]
    rw [funext h])

theorem whit_iSup_range_eq_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap = ⊤ := by
  intro k _ _ _ _ ψ d X _ _ ρ
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have hmem : Submodule.Quotient.mk (PiTensorProduct.tprod ℂ v) ∈
        ⨆ f : (ρ 0).IntertwiningMap (whit2 ψ d (piTensor ρ)), LinearMap.range f.toLinearMap := by
      refine Submodule.mem_iSup_of_mem (whitFirstMap ψ d ρ v) (LinearMap.mem_range.2 ⟨v 0, ?_⟩)
      show whitFirstLin ψ d ρ v (v 0) = _
      rw [whitFirstLin_apply, Function.update_eq_self]
    rw [Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem _ r hmem
  | add a b ha hb =>
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ ha hb

end GlobalTheory.CompanionTheory.BZNuPair
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.weighted_sum_decomposition_denominators : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ), (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧ (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧ ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int <;> assumption)
end
