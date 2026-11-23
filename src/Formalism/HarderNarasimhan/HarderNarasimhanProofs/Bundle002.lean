module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle001
public import Formalism.HarderNarasimhan.Bundle002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle001
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

theorem satBasic_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro x hx
  rw [satR_mem_zl] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, h hy, rfl⟩

theorem satBasic_zl_bot : zl ρ (⊥ : Submodule R V) = ⊥ := by
  ext x
  rw [satR_mem_zl, Submodule.mem_bot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]
  · intro hx
    exact ⟨0, Submodule.zero_mem _, by rw [hx, map_zero]⟩

end

theorem saturation_basic_properties : SatBasic := by
  intro R V E _ _ _ _ _ _ ρ L hL
  haveI hLd : DiscreteTopology (zl ρ L) := hL.2
  have hdisc : ∀ N : Submodule R V, N ≤ L → DiscreteTopology (zl ρ N) := fun N h =>
    Formalism.F.discreteTopology_of_le (satBasic_zl_mono ρ h)

  have hrev : ∀ A B : Submodule R V, A ≤ L → B ≤ L → zl ρ B ≤ zl ρ A → B ≤ A := by
    intro A B hAL hBL h y hy
    obtain ⟨z, hz, hzy⟩ := (satR_mem_zl ρ A _).mp (h ((satR_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩))
    have := hL.1 (hAL hz) (hBL hy) hzy
    rw [← this]; exact hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N h
    exact ⟨hL.1.mono (fun x hx => h hx), hdisc N h⟩
  · intro A B hAB hBL
    haveI := hdisc B hBL
    haveI := hdisc A (hAB.trans hBL)
    refine ⟨Formalism.F.att_rk_le (satBasic_zl_mono ρ hAB), fun hr => ?_⟩
    have hc := Formalism.F.covolAntiSameRank E (zl ρ A) (zl ρ B) (hdisc B hBL)
      (satBasic_zl_mono ρ hAB) hr
    have hpB := Formalism.F.covol_pos (zl ρ B)
    show -Real.log (Formalism.F.covol (zl ρ A)) ≤ -Real.log (Formalism.F.covol (zl ρ B))
    have := Real.log_le_log hpB hc
    linarith
  · intro S N hS hSN hNL hr
    haveI := hdisc N hNL
    refine le_antisymm (hrev S N hS.1 hNL ?_) hSN
    intro x hx
    obtain ⟨a, ha, hax⟩ :=
      exists_smul_mem_of_finrank_eq (zl ρ N) (zl ρ S) (satBasic_zl_mono ρ hSN) hr x hx
    refine hS.2.2 x (satBasic_zl_mono ρ hNL hx) ?_
    have hx' : x = (a : ℝ)⁻¹ • ((a : ℝ) • x) := by
      rw [inv_smul_smul₀ (by exact_mod_cast ha)]
    rw [hx']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact hax
  · intro N hNL
    haveI := hdisc N hNL
    constructor
    · intro h0
      have h0' : Formalism.F.rk (zl ρ N) = 0 := h0
      have hb : zl ρ N = ⊥ := by
        by_contra hne
        have := Formalism.F.att_rk_pos hne
        omega
      rw [eq_bot_iff]
      intro y hy
      have hy' : ρ y ∈ zl ρ N := (satR_mem_zl ρ N _).mpr ⟨y, hy, rfl⟩
      rw [hb, Submodule.mem_bot] at hy'
      rw [Submodule.mem_bot]
      exact hL.1 (hNL hy) (Submodule.zero_mem L) (by rw [hy', map_zero])
    · rintro rfl
      show Formalism.F.rk (zl ρ ⊥) = 0
      rw [satBasic_zl_bot ρ]
      simp [Formalism.F.rk]
  · show -Real.log (Formalism.F.covol (zl ρ ⊥)) = 0
    rw [satBasic_zl_bot ρ, (Formalism.F.covolBasic E).1]
    simp
  · refine ⟨bot_le, ?_⟩
    rw [satBasic_zl_bot ρ]
    refine ⟨bot_le, fun x _ hx => ?_⟩
    simpa using hx
  · exact ⟨le_rfl, le_rfl, fun x hx _ => hx⟩
  · intro S hS
    haveI := hdisc S hS.1
    obtain ⟨_, h2, h3⟩ := Formalism.F.degQuot E (zl ρ L) (zl ρ S) hLd hS.2
    refine ⟨?_, ?_, ?_⟩
    · show _ = Formalism.F.rk (zl ρ L) - Formalism.F.rk (zl ρ S)
      omega
    · show Formalism.F.rk (zl ρ S) ≤ Formalism.F.rk (zl ρ L)
      omega
    · show _ = Formalism.F.deg (zl ρ L) - Formalism.F.deg (zl ρ S)
      linarith

end Formalism.HN
end
end

section

open Module NumberField

noncomputable section

namespace Formalism.HN

def rscMap {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ) :
    EuclideanSpace ℝ (P × ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (P × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun p => (c p.1)⁻¹ • LinearMap.proj p) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (P × ι × Fin 2 → ℝ)).toLinearMap

theorem rscMap_apply {P ι : Type*} [Fintype P] [Fintype ι] (c : P → ℝ)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (p : P × ι × Fin 2) :
    rscMap c x p = (c p.1)⁻¹ * x p := by
  simp [rscMap, LinearMap.pi_apply]

theorem mem_placePart_iff {P ι : Type*} [Fintype P] [Fintype ι] (v : P)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) :
    x ∈ placePart (ι := ι) v ↔ ∀ p : P × ι × Fin 2, p.1 ≠ v → x p = 0 := by
  simp [placePart, Submodule.mem_iInf]

theorem inner_eq_sum_pl {P ι : Type*} [Fintype P] [Fintype ι]
    (x y : EuclideanSpace ℝ (P × ι × Fin 2)) :
    inner ℝ x y = ∑ p, x p * y p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [mul_comm]

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem realize_smul_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (c : InfinitePlace K → ℝ) (hX : ∀ v, IsUnit (X v).det) (hc : ∀ v, 0 < c v) (x : V) :
    Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x = rscMap c (Formalism.HermitianLatticesTheory.realize b X x) := by
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b (fun w => ((c w : ℂ)) • X w) v x =
      ((c v : ℂ))⁻¹ • Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
    have hi : ((c v : ℂ) • X v)⁻¹ = ((c v : ℂ))⁻¹ • (X v)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.nonsing_inv_mul _ (hX v)]
    simp only [Formalism.HermitianLatticesTheory.fcoord, hi]
    first
      | exact Matrix.smul_mulVec _ _ _
      | exact Matrix.smul_mulVec_assoc _ _ _
      | (funext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
  ext p
  rw [rscMap_apply]
  by_cases h : p.2.2 = 0
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  · have e1 : (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v) x) p =
        (Formalism.HermitianLatticesTheory.fcoord b (fun v => ((c v : ℂ)) • X v) p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    have e2 : (Formalism.HermitianLatticesTheory.realize b X x) p = (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by
      simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, h]
    rw [e1, e2, hf]
    simp [← Complex.ofReal_inv, Complex.im_ofReal_mul]
end

theorem rescaleCovol_of (h1 : PlaceSplit) (h2 : GramBlock) (h3 : PlLat) : RescaleCovol := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X c hX hc N hN
  have hX' : ∀ v, IsUnit (((c v : ℂ)) • X v).det := by
    intro v
    have hc0 : (c v : ℂ) ≠ 0 := by exact_mod_cast (hc v).ne'
    rw [Matrix.det_smul]
    exact (hc0.isUnit.pow _).mul (hX v)
  have hρ' := realize_smul_eq b X c hX hc
  have hinj : Function.Injective ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    intro x y hxy
    ext p
    have := congrArg (fun z => z p) hxy
    simp only [LinearMap.restrictScalars_apply, rscMap_apply] at this
    exact mul_left_cancel₀ (inv_ne_zero (hc p.1).ne') this
  have hL' : zl (Formalism.HermitianLatticesTheory.realize b (fun v => ((c v : ℂ)) • X v)) N =
      (zl (Formalism.HermitianLatticesTheory.realize b X) N).map ((rscMap (ι := ι) c).restrictScalars ℤ) := by
    ext y
    simp only [zl, Submodule.mem_map, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, (hρ' x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hρ' x⟩
  obtain ⟨⟨_, hLd⟩, -, -⟩ := h3 K V ι b X hX N hN
  obtain ⟨⟨_, hL'd⟩, -, -⟩ := h3 K V ι b _ hX' N hN
  rw [hL'] at hL'd ⊢
  have := hLd
  have := hL'd
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let L := zl (Formalism.HermitianLatticesTheory.realize b X) N
  let bL := Module.finBasis ℤ L
  let e := Submodule.equivMapOfInjective _ hinj L
  let bM := bL.map e
  have hbM : (fun i => (bM i : E)) = fun i => rscMap (ι := ι) c (bL i) := by
    funext i; simp [bM, e]
  rw [Formalism.F.covolEqGram _ _ _ bM, Formalism.F.covolEqGram _ L _ bL, hbM]
  have horth : ∀ v w : InfinitePlace K, v ≠ w → ∀ x ∈ placePart (ι := ι) v,
      ∀ y ∈ placePart (ι := ι) w, inner ℝ x y = 0 := by
    intro v w hvw x hx y hy
    rw [inner_eq_sum_pl]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : p.1 = v
    · rw [(mem_placePart_iff w y).1 hy p (by rw [hp]; exact hvw), mul_zero]
    · rw [(mem_placePart_iff v x).1 hx p hp, zero_mul]
  have hTinner : ∀ v, ∀ x ∈ placePart (ι := ι) v, ∀ y ∈ placePart (ι := ι) v,
      inner ℝ (rscMap c x) (rscMap c y) = (c v)⁻¹ ^ 2 * inner ℝ x y := by
    intro v x hx y hy
    rw [inner_eq_sum_pl, inner_eq_sum_pl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rscMap_apply, rscMap_apply]
    by_cases hp : p.1 = v
    · rw [hp]; ring
    · rw [(mem_placePart_iff v x).1 hx p hp]; ring
  have hTmap : ∀ v, ∀ x ∈ placePart (ι := ι) v,
      rscMap c x ∈ placePart (ι := ι) v ∧ ‖rscMap c x‖ ≤ (c v)⁻¹ * ‖x‖ := by
    intro v x hx
    refine ⟨(mem_placePart_iff v _).2 fun p hp => ?_, le_of_eq ?_⟩
    · rw [rscMap_apply, (mem_placePart_iff v x).1 hx p hp, mul_zero]
    · have h := hTinner v x hx x hx
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← mul_pow] at h
      exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.2 (hc v).le) (norm_nonneg _))
        two_ne_zero).1 h
  have hspZ : Submodule.span ℤ (Set.range fun i => (bL i : E)) = L := by
    have := congrArg (Submodule.map L.subtype) bL.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range fun i => (bL i : E)) = Submodule.span ℝ (L : Set E) := by
    apply le_antisymm
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (bL i).2)
    · refine Submodule.span_le.2 fun x hx => ?_
      rw [← hspZ] at hx
      exact Submodule.span_le_restrictScalars ℤ ℝ _ hx
  classical
  obtain ⟨hsplit, hdim⟩ := h1 K V ι b X hX N hN
  have hG := (h2 (InfinitePlace K) E E (Fin (finrank ℤ L)) (placePart (ι := ι)) (placePart (ι := ι))
    (rscMap c) (fun v => (c v)⁻¹) (Submodule.span ℝ (L : Set E)) (fun i => (bL i : E))
    horth horth (fun v => inv_nonneg.2 (hc v).le) hTmap hsplit
    (Formalism.F.linearIndependent_coe_basis''' L bL) hspan).2 hTinner
  have hdim' : ∀ v, finrank ℝ (Submodule.span ℝ (L : Set E) ⊓ placePart (ι := ι) v :
      Submodule ℝ E) = 2 * rkK N := hdim
  simp only [hdim'] at hG
  rw [hG, Real.sqrt_mul (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _)]
  congr 1
  have hsq : (∏ v, (c v)⁻¹ ^ (2 * (2 * rkK N))) = (∏ v, (c v)⁻¹ ^ (2 * rkK N)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    ring
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun v _ => pow_nonneg (inv_nonneg.2 (hc v).le) _),
    Real.rpow_neg (Finset.prod_nonneg fun v _ => (hc v).le),
    show (2 * (rkK N : ℝ)) = ((2 * rkK N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => inv_pow _ _

theorem rescale_covolume_formula : RescaleCovol := by
  exact rescaleCovol_of place_decomposition gram_block_determinant place_lattice_structure

end Formalism.HN
end
end
