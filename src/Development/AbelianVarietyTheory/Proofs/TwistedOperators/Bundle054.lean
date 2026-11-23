module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle048
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle046
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

section

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

section Indicator
open scoped Classical

variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he


open Classical in
theorem sum_target :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
  have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
    rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
  rw [midInd, mulVec_smul]
  split_ifs with h
  · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
      one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
    rw [Finset.sum_eq_single_of_mem (glue hg)]
    · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
    · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
        (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
    · exact fun Q₁ h1 h2 => if_neg fun h3 =>
        h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
  · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withKer] at h1
    exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩


open Classical in
theorem sum_source :
    midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
  rw [midInd]
  have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
  split_ifs with h
  · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
    have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
    have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
    let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
    have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
    rw [Finset.sum_eq_single_of_mem R]
    · exact (if_pos hR).symm
    · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
    · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
      have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
      rw [maps_iff_hasVal] at hR h3
      constructor
      · intro hy
        have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
      · intro hy
        have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
        exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
  · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withLat] at h1
    exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩

end Indicator

theorem card_withKer (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    (withKer L).card = (withLat L).card := by
  classical
  by_cases hfull : L.IsFullLattice k
  · letI : L.IsFullLattice k := hfull
    letI := Fintype.ofFinite (Red L)
    letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
    have hc : Fintype.card (Red L) = Fintype.card (Module.Dual 𝓀[k] (Red L)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := 𝓀[k]),
        Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := Module.Dual 𝓀[k] (Red L)), Subspace.dual_finrank_eq]
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat L]
    simp [hc]
  · have hk : withKer L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withKer.mp hP]
      exact P.ker_isLat)
    have hl : withLat L = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro P hP
      apply hfull
      rw [← mem_withLat.mp hP]
      exact P.isLat)
    simp [hk, hl]

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem exists_det (q : Unif k) (P : Pair k n) :
    ∃ d : GL n k, d • P.ker = P.lat ∧ Matrix.GeneralLinearGroup.det d = q.unit⁻¹ := by
  obtain ⟨i⟩ : Nonempty n := by
    by_contra h
    haveI := not_nonempty_iff.1 h
    exact P.fn_ne (LinearMap.ext fun y => by rw [Subsingleton.elim y 0]; simp)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  have hdet : (Matrix.diagonal (Function.update (1 : n → k) i (q.1 : k))).det = (q.1 : k) := by
    simp [Matrix.det_diagonal, Finset.prod_update_of_mem]
  let d : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ q.ne_zero)
  have hd : ∀ (y : n → k) j, (d • y) j = Function.update (1 : n → k) i (q.1 : k) j * y j := fun y j =>
    Matrix.mulVec_diagonal _ _ _
  have h1 : d⁻¹ • (stdPair k i).ker = (stdPair k i).lat := by
    ext y
    rw [mem_smul_iff, inv_inv, Pair.mem_ker, stdPair_hasVal]
    change _ ↔ y ∈ stdLat k n
    rw [mem_stdLat]
    constructor
    · rintro ⟨h, h0⟩ j
      by_cases hj : j = i
      · subst hj
        obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff _).1 h0)
        have h2 : (q.1 : k) * y j = q.1 * s := by simpa [hd] using congrArg Subtype.val hs
        rw [mul_left_cancel₀ q.ne_zero h2]
        exact s.2
      · simpa [hd, hj] using h j
    · intro h
      refine ⟨fun j => ?_, (residue_eq_zero_iff _).2 (q.mem_max_iff.2 ⟨⟨y i, h i⟩, Subtype.ext (by simp [hd])⟩)⟩
      by_cases hj : j = i
      · subst hj
        simpa [hd] using mul_mem q.1.2 (h j)
      · simpa [hd, hj] using h j
  refine ⟨a * d⁻¹ * a⁻¹, by rw [Pair.smul_ker, Pair.smul_lat, mul_smul, mul_smul, inv_smul_smul, h1], ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, _root_.inv_inj]
  exact Units.ext hdet

theorem valuation_det (q : Unif k) (P : Pair k n) {g : GL n k} (hg : g • P.ker = P.lat) :
    valuation k ((Matrix.GeneralLinearGroup.det g * q.unit : kˣ) : k) = 1 := by
  obtain ⟨d, hd, hdet⟩ := exists_det q P
  have := valuation_det_of_fix P.ker (h := d⁻¹ * g) (by rw [mul_smul, hg, ← hd, inv_smul_smul])
  rwa [map_mul, map_inv, hdet, inv_inv, mul_comm] at this

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

theorem eq_of_base {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]

end GlobalTheory.KernelComm
end
end

section

open MeasureTheory GlobalTheory.FunObj

noncomputable section
namespace GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitsPowInv_val (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

theorem resMk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  have h0 : (ϖ : k) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    unitsPowInv_val]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (a : k) - b = (ϖ : k) ^ e * c := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [h1, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem mem_of_inv_mul_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by
  have hx : x = (ϖ : k) ^ e * ((((ϖ ^ e)⁻¹ : kˣ) : k) * x) := by
    rw [unitsPowInv_val, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  rw [hx]
  exact mul_mem (pow_mem hϖ.mem _) h

theorem mem_matLat_pow_smul_iff (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] :=
  ⟨fun h i j => mem_stdLat.1 ((mem_smul_lat _ _ _).1 (h i)) j,
   fun h i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => h i j)⟩

def resClass (ϖ : kˣ) {e : ℕ} {m n : ℕ} (c : Fin m → Fin n → Res k e) : Set (Matrix (Fin m) (Fin n) k) :=
  {X | ∀ i j, X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k]}

theorem isNatDatum_resClass {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {m n : ℕ} (c : Fin m → Fin n → Res k e) :
    IsNatDatum ϖ e ((resClass ϖ c).indicator (1 : Matrix (Fin m) (Fin n) k → ℂ)) := by
  classical
  refine ⟨fun X hX => Set.indicator_of_notMem (fun h => hX (mem_matLat_stdLat.2 fun i j => (h i j).1)) _,
    fun X Z hZ => ?_⟩
  have hZ' := (mem_matLat_pow_smul_iff ϖ e).1 hZ
  have hiff : X + Z ∈ resClass ϖ c ↔ X ∈ resClass ϖ c := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have hz : Z i j ∈ 𝒪[k] := mem_of_inv_mul_mem hϖ e (hZ' i j)
    have h1 : (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) =
        (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) + (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j := by ring
    show (X i j + Z i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) ∈ 𝒪[k]) ↔
      (X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k])
    rw [h1, add_mem_cancel_right hz, add_mem_cancel_right (hZ' i j)]
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

theorem exists_sum_pureTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  intro k _ _ _ _ G ϖ hϖ e γ T hT
  classical
  let L := γ.toFinset
  let I := ∀ b : L, Fin (G.rank b.1.tgt) → Fin (G.rank b.1.src) → Res k e
  let rep : I → G.Args := fun c b => if h : b ∈ L then liftRes (c ⟨b, h⟩) else 0
  let ψ : I → ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ :=
    fun c b => if h : b ∈ L then (resClass ϖ (c ⟨b, h⟩)).indicator 1 else 1
  have key : ∀ z, T z = ∑ c, T (rep c) * G.lines₂ γ (ψ c) z := by
    intro z
    simp only [Grid.lines₂]
    by_cases hint : ∀ b ∈ γ, z b ∈ matLat _ (stdLat k _)
    · let c0 : I := fun b i j => Ideal.Quotient.mk _
        ⟨z b.1 i j, mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2)) i j⟩
      have hmem : ∀ (c : I) (b : L), z b.1 ∈ resClass ϖ (c b) ↔ c b = c0 b := by
        intro c b
        have hz := mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2))
        constructor
        · intro h
          funext i j
          have := (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).2 (h i j).2
          rw [Ideal.Quotient.mk_out] at this
          exact this.symm
        · rintro h i j
          refine ⟨hz i j, ?_⟩
          exact (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).1
            (by rw [Ideal.Quotient.mk_out, h])
      rw [Finset.sum_eq_single c0]
      · have hprod : (γ.map fun b => ψ c0 b (z b)).prod = 1 := by
          refine List.prod_eq_one fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have hb' : b ∈ L := List.mem_toFinset.2 hb
          simp only [ψ, dif_pos hb']
          exact Set.indicator_of_mem ((hmem c0 ⟨b, hb'⟩).2 rfl) _
        rw [hprod, mul_one]
        let w : G.Args := fun b => if b ∈ γ then z b - rep c0 b else 0
        have hw : ∀ b, w b ∈ matLat _ (ϖ ^ e • stdLat k _) := by
          intro b
          by_cases hb : b ∈ γ
          · have hb' : b ∈ L := List.mem_toFinset.2 hb
            have h2 := (hmem c0 ⟨b, hb'⟩).2 rfl
            refine (mem_matLat_pow_smul_iff ϖ e).2 fun i j => ?_
            simp only [w, if_pos hb, rep, dif_pos hb', Matrix.sub_apply]
            exact (h2 i j).2
          · simp only [w, if_neg hb]
            exact zero_mem _
        rw [← hT.2.2 (rep c0) w hw]
        refine hT.1 fun b hb => ?_
        have hb : b ∈ γ := hb
        simp [w, hb]
      · intro c _ hc
        obtain ⟨b, hb⟩ : ∃ b : L, c b ≠ c0 b := by
          by_contra hne
          push_neg at hne
          exact hc (funext hne)
        rw [List.prod_eq_zero (List.mem_map.2 ⟨b.1, List.mem_toFinset.1 b.2, ?_⟩), mul_zero]
        simp only [ψ, dif_pos b.2]
        exact Set.indicator_of_notMem (mt (hmem c b).1 hb) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hint
      obtain ⟨b, hb, hz⟩ := hint
      rw [hT.2.1 z b hb hz]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, ?_⟩), mul_zero]
      have hb' : b ∈ L := List.mem_toFinset.2 hb
      simp only [ψ, dif_pos hb']
      have hn : z b ∉ resClass ϖ (c ⟨b, hb'⟩) := fun h =>
        hz (mem_matLat_stdLat.2 fun i j => (h i j).1)
      exact Set.indicator_of_notMem hn _
  refine ⟨Fintype.card I, fun i => T (rep ((Fintype.equivFin I).symm i)),
    fun i => ψ ((Fintype.equivFin I).symm i), ?_, ?_⟩
  · intro i b hb
    have hb' : b ∈ L := List.mem_toFinset.2 hb
    simp only [ψ, dif_pos hb']
    exact isNatDatum_resClass hϖ e _
  · intro z
    rw [key z]
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun c => T (rep c) * G.lines₂ γ (ψ c) z)).symm

end GlobalTheory.TensorExpansion
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.SplitWeil

private lemma rpow_half_mul_rpow_inv_eq_one (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * ((t⁻¹) ^ (-a) * s ^ (-b)) = 1 := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_neg]
  have e1 : s ^ (b / 2) * s ^ (b / 2) * s ^ (-b) = 1 := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs, show b / 2 + b / 2 + -b = (0 : ℝ) by ring, Real.rpow_zero]
  have e2 : t ^ (-a / 2) * t ^ (-a / 2) * t ^ a = 1 := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, show -a / 2 + -a / 2 + a = (0 : ℝ) by ring, Real.rpow_zero]
  calc s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * (t ^ a * s ^ (-b))
      = (s ^ (b / 2) * s ^ (b / 2) * s ^ (-b)) * (t ^ (-a / 2) * t ^ (-a / 2) * t ^ a) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

private lemma isUnit_of_valuation_eq_one' (z : ℂ) (hz : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

private lemma unit_mul_real_mul_conj_eq_real_sq_mul (m1 m2 : ℂ) (h1 : ‖m1‖ = 1) (h2 : ‖m2‖ = 1) (r1 r2 : ℝ) (u v : ℂ) :
    m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * u * (starRingEnd ℂ) (m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * v) =
      ((r1 * r2 * (r1 * r2) : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) := by
  have e1 := isUnit_of_valuation_eq_one' m1 h1
  have e2 := isUnit_of_valuation_eq_one' m2 h2
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination (m2 * (starRingEnd ℂ) m2 * r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e1 +
    (r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e2

private lemma nabs_pos_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit x).map (distribHaarChar k)).ne_zero)

private lemma nabs_inv_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  show ((distribHaarChar k x⁻¹ : NNReal) : ℝ) = ((distribHaarChar k x : NNReal) : ℝ)⁻¹
  rw [map_inv, NNReal.coe_inv]

theorem ip_om_om : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : ∀ x, ‖(μ x : ℂ)‖ = 1) (g : GL a k) (h : GL b k) (Φ Ψ : Matrix b a k → ℂ), ip ν (om μ g h Φ) (om μ g h Ψ) = ip ν Φ Ψ := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _ μ hμ g h Φ Ψ
  set F : Matrix b a k → ℂ := fun y => Φ y * (starRingEnd ℂ) (Ψ y) with hF
  have hinv : ‖(((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hμ, inv_one]
  set ng := nabs k (Matrix.GeneralLinearGroup.det g) with hng
  set nh := nabs k (Matrix.GeneralLinearGroup.det h) with hnh
  set c : ℝ := ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2) *
    (ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2)) with hc
  have hpt : ∀ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) =
      (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) := fun x =>
    unit_mul_real_mul_conj_eq_real_sq_mul _ _ (hμ _) hinv _ _ _ _
  have hT := (GlobalTheory.T.linear_change_of_variables_localField_matrix k a b ν).2 g h⁻¹ F
  have hdet : nabs k (Matrix.GeneralLinearGroup.det h⁻¹) = nh⁻¹ := by
    rw [map_inv, nabs_inv_twisted_operators]
  have hkey : c * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
      ng ^ (-(Fintype.card b : ℝ))) = 1 := by
    rw [hdet]
    exact rpow_half_mul_rpow_inv_eq_one ng nh (nabs_pos_twisted_operators k _) (nabs_pos_twisted_operators k _) _ _
  unfold ip
  calc ∫ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) ∂(volM ν b a)
      = ∫ x, (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := by
        congr 1
        funext x
        exact hpt x
    _ = (c : ℂ) * ∫ x, F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := integral_const_mul _ _
    _ = ∫ x, F x ∂(volM ν b a) := by
        rw [hT, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hkey, Complex.ofReal_one, one_mul]

end GlobalTheory.SplitWeil
end
