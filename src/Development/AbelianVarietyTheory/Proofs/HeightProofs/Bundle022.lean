module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle008
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle021
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Matrix

namespace GlobalTheory.RealPar

variable {p q n : ℕ}

def BlockOrd (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) ∧ ∀ a b, posC a b → e a < e b

def Factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)) : Prop :=
  ∀ x, U.π x = σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))

theorem BlockOrd.sameBlock_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    sameBlock a b ↔ ε (e a) = ε (e b) := by
  obtain ⟨h1, h2, -⟩ := h
  cases a <;> cases b <;> simp [sameBlock, h1, h2]

theorem BlockOrd.posC_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    posC a b ↔ e a < e b ∧ ε (e a) = ε (e b) := by
  constructor
  · intro hab
    refine ⟨h.2.2 a b hab, ?_⟩
    rw [← h.sameBlock_iff]
    cases a <;> cases b <;> simp_all [posC, sameBlock]
  · rintro ⟨hlt, heq⟩
    rw [← h.sameBlock_iff] at heq
    have hne : a ≠ b := fun hab => by subst hab; exact lt_irrefl _ hlt
    have hnot : ¬ posC b a := fun hba => lt_asymm hlt (h.2.2 b a hba)
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inl hij) hne
        · exact absurd hij hnot
      | inr j => simp [sameBlock] at heq
    | inr i =>
      cases b with
      | inl j => simp [sameBlock] at heq
      | inr j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inr hij) hne
        · exact absurd hij hnot

theorem exists_blockOrd (ε : Fin n → Bool) (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : ∃ e : Ix p q ≃ Fin n, BlockOrd e ε := by
  classical
  set S := Finset.univ.filter fun a => ε a = true with hS
  set T := Finset.univ.filter fun a => ε a = false with hT
  have hcard : p + q = n := by
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun a => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h0
    rw [← hp, ← hq]
    exact h0
  let f : Ix p q → Fin n := fun x =>
    match x with
    | Sum.inl i => S.orderEmbOfFin hp i
    | Sum.inr j => T.orderEmbOfFin hq j
  have fS : ∀ i, ε (f (Sum.inl i)) = true := fun i =>
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem hp i)).2
  have fT : ∀ j, ε (f (Sum.inr j)) = false := fun j =>
    (Finset.mem_filter.mp (T.orderEmbOfFin_mem hq j)).2
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl ((S.orderEmbOfFin hp).injective hxy)
      | inr j =>
        have h1 := fS i
        rw [hxy, fT j] at h1
        exact absurd h1 (by simp)
    | inr i =>
      cases y with
      | inl j =>
        have h1 := fT i
        rw [hxy, fS j] at h1
        exact absurd h1 (by simp)
      | inr j => exact congrArg Sum.inr ((T.orderEmbOfFin hq).injective hxy)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [hcard]
  refine ⟨Equiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro i
    exact fS i
  · intro j
    exact fT j
  · intro a b hab
    simp only [Equiv.ofBijective_apply]
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (S.orderEmbOfFin hp).strictMono hab
      | inr j => exact absurd hab (by simp [posC])
    | inr i =>
      cases b with
      | inl j => exact absurd hab (by simp [posC])
      | inr j => exact (T.orderEmbOfFin hq).strictMono hab

theorem BlockOrd.reindex_Jm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    Matrix.reindex e e (Jm p q) = Formalism.REAL.Jm ε := by
  obtain ⟨h1, h2, -⟩ := h
  ext a b
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Jm, Formalism.UG.Jpq]
  cases a' <;> cases b' <;> simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp

theorem BlockOrd.inUJ_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (g : Mat p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e g) ↔ gᴴ * Jm p q * g = Jm p q := by
  have key : ∀ M N : Mat p q, Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inUJ
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex, key, key]
  exact (Matrix.reindex e e).injective.eq_iff

theorem mem_Upq (g : GL (Ix p q) ℂ) : g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Jm p q * g = Jm p q := by
  unfold Formalism.UG.Upq Formalism.UG.UJ
  rw [Subgroup.mem_mk]
  show Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q ↔ _
  have hc : Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) = (g : Mat p q)ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hc]
  rfl

theorem BlockOrd.cov_mem {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  exact (h.inUJ_iff _).mpr ((mem_Upq _).mp (T.cov_mem x))

theorem BlockOrd.cov_surj {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ x : T.G, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  have hg' : Formalism.REAL.inUJ ε g := hg
  set g' : Mat p q := (Matrix.reindex e e).symm g
  have hre : Matrix.reindex e e g' = g := (Matrix.reindex e e).apply_symm_apply g
  have hU : g'ᴴ * Jm p q * g' = Jm p q := by
    rw [← h.inUJ_iff, hre]
    exact hg'
  have hJJ : Jm p q * Jm p q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hleft : (Jm p q * g'ᴴ * Jm p q) * g' = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hU, hJJ]
  have hright : g' * (Jm p q * g'ᴴ * Jm p q) = 1 := mul_eq_one_comm.mp hleft
  let u : GL (Ix p q) ℂ := ⟨g', Jm p q * g'ᴴ * Jm p q, hright, hleft⟩
  have hu : u ∈ Formalism.UG.Upq p q := (mem_Upq u).mpr hU
  have hdet : (u : Mat p q).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (u : Mat p q)).mp u.isUnit
    exact this.ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Mat p q).det (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hz]; simp)
  obtain ⟨x, ⟨hx, -⟩, -⟩ := T.bij u hu (Units.mk0 z hz0) (by simpa using hz)
  refine ⟨x, ?_⟩
  rw [hx]
  exact hre

theorem exists_factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (h : ∀ x, T.cov x = 1 → U.π x = 1) : ∃ σ, Factors U e σ := by
  classical
  refine ⟨fun M => if hM : ∃ x, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = M
    then U.π hM.choose else 0, ?_⟩
  intro x
  have hM : ∃ y, Matrix.reindex e e ((T.cov y : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := ⟨x, rfl⟩
  simp only [dif_pos hM]
  set y := hM.choose with hy
  have hyx : T.cov y = T.cov x := Units.ext ((Matrix.reindex e e).injective hM.choose_spec)
  have h1 : T.cov (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : U.π y⁻¹ * U.π x = 1 := by
    rw [← map_mul]
    exact h _ h1
  calc U.π x = U.π (y * y⁻¹) * U.π x := by simp
    _ = U.π y * (U.π y⁻¹ * U.π x) := by rw [map_mul, mul_assoc]
    _ = U.π y := by rw [h2, mul_one]

end GlobalTheory.RealPar

end
end

section

open Formalism.MainNotions.S Matrix MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

namespace SchurOrth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}

theorem exists_coefMap (π : G → (H →L[ℂ] H)) (w : H)
    (h : ∀ v : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) :
    ∃ T : H →L[ℂ] Lp ℂ 2 μ, ∀ v, (T v : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g v⟫_ℂ := by
  let L : H →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun v => (h v).toLp _
      map_add' := fun a b => by
        rw [← MemLp.toLp_add]
        congr 1
        ext g
        simp [inner_add_right]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        ext g
        simp [inner_smul_right] }
  have hL : ∀ v, (L v : G → ℂ) =ᵐ[μ] fun g => ⟪w, π g v⟫_ℂ := fun v => (h v).coeFn_toLp
  have hc : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u x y hu hy => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hy).exists_seq_tendsto_ae
    have hall : ∀ᵐ g ∂μ, ∀ i, (L (u i) : G → ℂ) g = ⟪w, π g (u i)⟫_ℂ :=
      ae_all_iff.2 fun i => hL (u i)
    refine Lp.ext ?_
    filter_upwards [hae, hall, hL x] with g h1 h2 h3
    rw [h3]
    have h4 : Filter.Tendsto (fun i => ⟪w, π g (u (ns i))⟫_ℂ) Filter.atTop (nhds ⟪w, π g x⟫_ℂ) :=
      Filter.Tendsto.inner tendsto_const_nhds
        (((π g).continuous.tendsto x).comp (hu.comp hns.tendsto_atTop))
    refine tendsto_nhds_unique h1 ?_
    simpa only [Function.comp_apply, h2] using h4
  exact ⟨⟨L, hc⟩, hL⟩

omit [CompleteSpace H] [MeasurableSpace G] in
theorem inner_rep (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (a b : H) :
    ⟪a, π g b⟫_ℂ = ⟪π g⁻¹ a, b⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := ⟨(π g : H →ₗ[ℂ] H), hπ g⟩
  have h1 := e.inner_map_map (π g⁻¹ a) b
  have h2 : π g (π g⁻¹ a) = a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [← h1]
  change _ = ⟪π g (π g⁻¹ a), π g b⟫_ℂ
  rw [h2]

theorem schur_orthogonality [Nontrivial H] [TopologicalSpace G] [MeasurableMul G] [MeasurableInv G]
    [μ.IsOpenPosMeasure] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (π : G →* (H →L[ℂ] H)) (hπ : ∀ g v, ‖π g v‖ = ‖v‖) (hc : ∀ v, Continuous fun g => π g v)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (h : ∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ) :
    ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  choose T hT using fun w => exists_coefMap (μ := μ) π w (fun v => h v w)
  let I : H → H → H → H → ℂ := fun v w v' w' => ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ ∂μ
  have hae : ∀ v w v' w', (fun g => ⟪(T w' v' : G → ℂ) g, (T w v : G → ℂ) g⟫_ℂ) =ᵐ[μ]
      fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ := by
    intro v w v' w'
    filter_upwards [hT w v, hT w' v'] with g h1 h2
    rw [h1, h2, RCLike.inner_apply]
    rfl
  have hint : ∀ v w v' w', Integrable (fun g => ⟪w, π g v⟫_ℂ * star ⟪w', π g v'⟫_ℂ) μ :=
    fun v w v' w' => (L2.integrable_inner (𝕜 := ℂ) (T w' v') (T w v)).congr (hae v w v' w')
  have hI : ∀ v w v' w',
      ⟪v', ((ContinuousLinearMap.adjoint (T w')).comp (T w)) v⟫_ℂ = I v w v' w' := by
    intro v w v' w'
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
    exact integral_congr_ae (hae v w v' w')
  have hsc : ∀ w w', ∃ c : ℂ, ∀ v v', I v w v' w' = c * ⟪v', v⟫_ℂ := by
    intro w w'
    obtain ⟨c, hc⟩ := GlobalTheory.T.hilbert_schur_unitary_irreducible_scalar H G π hπ hirr
      ((ContinuousLinearMap.adjoint (T w')).comp (T w)) (by
        intro g
        ext v
        refine ext_inner_left ℂ fun v' => ?_
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, inner_rep π hπ, hI, hI]
        simp only [I]
        rw [← integral_mul_right_eq_self _ g]
        congr 1
        ext x
        rw [← ContinuousLinearMap.mul_apply (π (x * g)) (π g⁻¹), ← map_mul, mul_inv_cancel_right,
          map_mul, ContinuousLinearMap.mul_apply])
    refine ⟨c, fun v v' => ?_⟩
    rw [← hI, hc]
    simp [inner_smul_right]
  choose c hcI using hsc
  have hsym : ∀ v w v' w', I v w v' w' = I w' v' w v := by
    intro v w v' w'
    simp only [I]
    rw [← integral_inv_eq_self]
    congr 1
    ext x
    rw [inner_rep π hπ x⁻¹, inner_rep π hπ x⁻¹, inv_inv, mul_comm]
    simp [inner_conj_symm]
  obtain ⟨u, hu⟩ : ∃ u : H, ‖u‖ = 1 := exists_norm_eq H zero_le_one
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have hpt : ∀ g, ⟪u, π g u⟫_ℂ * star ⟪u, π g u⟫_ℂ = ((‖⟪u, π g u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ := by
    refine integral_pos_of_integrable_nonneg_nonzero (x := 1) ?_ ?_ (fun g => by positivity) ?_
    · exact ((continuous_const.inner (hc u)).norm).pow 2
    · exact (h u u).integrable_norm_pow (by norm_num)
    · simp [hu]
  have hcu : c u u = ((∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    have := hcI u u u u
    rw [huu, mul_one] at this
    rw [← this, ← integral_complex_ofReal]
    simp only [I, hpt]
  refine ⟨(∫ g, ‖⟪u, π g u⟫_ℂ‖ ^ 2 ∂μ)⁻¹, inv_pos.2 hpos, fun v w v' w' => ⟨hint v w v' w', ?_⟩⟩
  have h1 : c w w' = c u u * ⟪w, w'⟫_ℂ := by
    rw [← hcI, ← hsym, hcI, huu, mul_one]
  change I v w v' w' = _
  rw [hcI, h1, hcu, Complex.ofReal_inv, div_inv_eq_mul]
  ring

end SchurOrth

theorem schur_orthogonality_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSqIntOn ε σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  intro n ε H _ _ _ _ σ hU hirr hsq
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hU
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  let π : Formalism.REAL.UJ ε →* (H →L[ℂ] H) :=
    { toFun := fun g => σ (umat g)
      map_one' := h1
      map_mul' := fun a b => hmul _ (hmem a) _ (hmem b) }
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsInvInvariant :=
    ⟨Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular n ε⟩
  exact SchurOrth.schur_orthogonality (μ := Formalism.REAL.muG ε) π (fun g v => hiso _ (hmem g) v)
    (fun v => (hcont v).comp_continuous (Formalism.REAL.continuous_coeMatrix ε) hmem)
    (fun S hS hst => hirr S hS fun g hg v hv => hst (Formalism.REAL.indefiniteUnitaryMk ε g hg) v hv) hsq

end GlobalTheory
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.weber_values_congruences_mod_degree_one_prime : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  first | exact @GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | exact GlobalTheory.WeberCongruenceAnyOrder.weber_congruences | (intros; apply GlobalTheory.WeberCongruenceAnyOrder.weber_congruences <;> assumption)
end
