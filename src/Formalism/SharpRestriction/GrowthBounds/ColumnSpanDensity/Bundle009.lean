module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle008
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def TiePsi : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    Function.Injective (PsiXY R.Kf m) ∧
    (∀ (P Q : ℕ) x, x ∈ twoSp R.Kf m P Q ↔ ∃ f ∈ PolAB R.Kf (m + 1) P Q, PsiXY R.Kf m f = x) ∧
    (∀ (a b : ℕ) y, y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) ↔
      ∃ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = y) ∧
    (∀ (a b : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = 0 →
      ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), f = hXY R.Kf (m + 1) * G) ∧
    ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
      ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) P Q,
          PsiXY R.Kf m f ∈ twoLat R.O m P Q Λ ↔ f ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) y, y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f ∈ PolAB R.Kf (m + 1) a b, f ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            deltaB R.Kf m (PsiXY R.Kf m f) = y)

theorem model_identification_of_explicit_map (h : TiePsi) : TwoLetterModelIdentification := by
  intro p n' R m hm
  obtain ⟨hinj, hsp, hdw, hker, hlat⟩ := h p n' R m hm
  let e : ∀ P Q : ℕ, PolAB R.Kf (m + 1) P Q →ₗ[R.Kf] twoSp R.Kf m P Q := fun P Q =>
    ((PsiXY R.Kf m).toLinearMap.domRestrict (PolAB R.Kf (m + 1) P Q)).codRestrict (twoSp R.Kf m P Q)
      (fun f => (hsp P Q _).2 ⟨f.1, f.2, rfl⟩)
  have he : ∀ P Q, Function.Bijective (e P Q) := fun P Q => by
    refine ⟨fun f g hfg => Subtype.ext (hinj (congrArg Subtype.val hfg)), fun x => ?_⟩
    obtain ⟨f, hf, hfx⟩ := (hsp P Q x.1).1 x.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  let α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q := fun P Q =>
    (LinearEquiv.ofBijective (e P Q) (he P Q)).symm
  have hαe : ∀ P Q (x : twoSp R.Kf m P Q),
      PsiXY R.Kf m (α P Q x : PolXY R.Kf (m + 1)) = x := fun P Q x => by
    have h1 := (LinearEquiv.ofBijective (e P Q) (he P Q)).apply_symm_apply x
    exact congrArg Subtype.val h1
  let β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) :=
    fun a b => (((deltaB R.Kf m).comp (PsiXY R.Kf m)).toLinearMap.domRestrict
      (PolAB R.Kf (m + 1) a b)).codRestrict _ (fun f => (hdw a b _).2 ⟨f.1, f.2, rfl⟩)
  have hβ : ∀ a b (f : PolAB R.Kf (m + 1) a b),
      (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = deltaB R.Kf m (PsiXY R.Kf m f) :=
    fun a b f => rfl
  have ha : ∀ i, deltaB R.Kf m (PsiXY R.Kf m (X (Sum.inl i))) = X (i, (0 : Fin (m + 1))) := by
    intro i
    simp only [PsiXY, aeval_X, Sum.elim_inl, deltaB, rename_X]
  have hc : ∀ i, deltaB R.Kf m (PsiXY R.Kf m (X (Sum.inr i))) = covY R.Kf m i := by
    intro i
    simp only [PsiXY, aeval_X, Sum.elim_inr, deltaB, rename_rename]
    rw [show (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id from rfl,
      rename_id, AlgHom.id_apply]
  have hh0 : deltaB R.Kf m (PsiXY R.Kf m (hXY R.Kf (m + 1))) = 0 := by

    simp only [hXY, map_sum, map_mul, ha, hc]
    exact sum_covY R.Kf m (by omega)
  refine ⟨α, β, ?_, ?_, ?_⟩
  · intro a b y
    obtain ⟨f, hf, hfy⟩ := (hdw a b y.1).1 y.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  · intro a b f
    constructor
    · intro h0
      have h1 : deltaB R.Kf m (PsiXY R.Kf m f) = 0 := by
        rw [← hβ]
        exact congrArg Subtype.val h0
      exact hker a b f.1 f.2 h1
    · rintro ⟨G, _, hfG⟩
      apply Subtype.ext
      rw [hβ, hfG, map_mul, map_mul, hh0, zero_mul]
      rfl
  · intro Λ hΛ
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    refine ⟨g', fun P Q x => ?_, fun a b y => ?_⟩
    · constructor
      · intro hx
        have hxs := twoLat_le_twoSp m P Q Λ hΛ x hx
        refine ⟨hxs, ?_⟩
        rw [← h1 P Q _ (α P Q ⟨x, hxs⟩).2, hαe]
        exact hx
      · rintro ⟨hxs, hl⟩
        have h3 := (h1 P Q _ (α P Q ⟨x, hxs⟩).2).2 hl
        rwa [hαe] at h3
    · rw [h2 a b y]
      constructor
      · rintro ⟨f, hf, hl, hfy⟩
        exact ⟨⟨f, hf⟩, hl, hfy⟩
      · rintro ⟨f, hl, hfy⟩
        exact ⟨f.1, f.2, hl, hfy⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

theorem filter_lt_one (m : ℕ) : (Finset.univ.filter fun a : Fin (m + 1) => a.val < 1) = {0} := by
  ext a
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    exact Fin.ext (by simpa using Nat.lt_one_iff.1 h)
  · rintro rfl
    exact ⟨Finset.mem_univ _, by simp⟩

theorem lamAt_abs {n' m : ℕ} (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) (s : Fin n')
    (i : Fin (m + 1)) : |lamAt lamO s i| ≤ c := by
  unfold lamAt
  split_ifs
  · exact h s i
  · rw [abs_neg]; exact h s _

section

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

def Elast (lamO : Fin n' → Fin (m + 1) → ℤ) : ℤ := ∑ s, lamAt lamO s (Fin.last m)

theorem Ar_sub_le (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) :
    Ar 1 lamO - Elast lamO ≤ ((2 * n' * c : ℕ) : ℤ) := by
  unfold Ar Elast
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ s ∈ (Finset.univ : Finset (Fin n')),
      (∑ i : Fin (m + 1) with i.val < 1, lamAt lamO s i) - lamAt lamO s (Fin.last m) ≤ 2 * (c : ℤ) := by
    intro s _
    rw [filter_lt_one, Finset.sum_singleton]
    have h2 := abs_le.1 (lamAt_abs lamO c h s 0)
    have h3 := abs_le.1 (lamAt_abs lamO c h s (Fin.last m))
    linarith [h2.2, h3.1]
  have h4 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h4
  refine le_trans h4 ?_
  push_cast
  rw [nsmul_eq_mul]
  linarith

theorem steps_rev (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO) (e : Edge R.W R.Qq (m + 1))
    (he : IsEdge p n' 1 e) :
    (∀ P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.src)) ∧
    (∀ P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.tgt),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e)) := by
  obtain ⟨gs, hgs, h1, h2, h3⟩ := edgeLat_RS R e he
  have hw := R.w_ne
  have hinj : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hA : ∏ s : Fin n', algebraMap R.O R.Kf R.w ^ (-lamAt lamO s (Fin.last m)) =
      algebraMap R.O R.Kf R.w ^ (-Elast lamO) := by
    rw [lb_zpow_sum _ hw, Elast, Finset.sum_neg_distrib]
  have hgD : ∀ s, IsUnit (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w)).det := by
    intro s
    rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hw)
  have hone : ∀ z : ℤ, -(((Finset.univ.filter fun a : Fin (m + 1) => a.val < 1).card : ℤ) * z) = -z := by
    intro z
    rw [filter_lt_one]
    simp
  constructor
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h2] at hF
    rw [h1]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgs _) F hF
    rwa [hone] at this
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h3] at hF
    rw [h2]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgD _) F hF
    rwa [hone] at this

end

theorem restOrdBound : RestOrdBound := by
  intro p n' R m lamO c hdom hsmall e he
  obtain ⟨hs1, hs2⟩ := steps_rev R lamO hdom e he
  have hw := R.w_ne
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hle := Ar_sub_le lamO c hsmall
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (k₀ : ℤ) = ((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO) :=
    ⟨(((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO)).toNat, Int.toNat_of_nonneg (by linarith)⟩
  constructor
  · rintro _ ⟨h, hh, rfl⟩
    have h1 : wK ^ (-Elast lamO) • h ∈ HL (O := R.O) R.ι R.σ lamO e.src := hs1 _ hh
    refine ⟨R.w ^ k₀ • (wK ^ (-Elast lamO) • h), Submodule.smul_mem _ _ h1, ?_⟩
    show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (R.w ^ k₀ • (wK ^ (-Elast lamO) • h)) = wK ^ (-Ar 1 lamO) • h
    rw [← algebraMap_smul R.Kf (R.w ^ k₀), map_pow, ← hwK, smul_smul, smul_smul, ← zpow_natCast wK k₀, hk₀,
      ← zpow_add₀ hw, ← zpow_add₀ hw]
    congr 2
    ring
  · rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ, ?_, ?_⟩
    · intro h hh
      have h1 : wK ^ (-Elast lamO) • h ∈ HLe p R.ι R.σ R.w lamO e := hs2 _ hh
      obtain ⟨a, ha⟩ := hφ _ h1
      refine ⟨R.w ^ k₀ * a, ?_⟩
      rw [map_smul, smul_eq_mul] at ha
      rw [map_mul, ha, map_pow, ← hwK, LinearMap.smul_apply, smul_eq_mul, ← zpow_natCast wK k₀, hk₀, ← mul_assoc,
        ← zpow_add₀ hw]
      congr 2
      ring
    · show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ) = wK ^ (-Ar 1 lamO) • φ
      rw [smul_smul, ← zpow_add₀ hw]
      congr 2
      ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Tr

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem mapM_det_unit (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    IsUnit (mapM (Qq := R.Qq) V).det := by
  show IsUnit ((algebraMap R.W R.Qq).mapMatrix V).det
  rw [← RingHom.map_det]
  exact hV.map _

theorem colSpan_mapM (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) :
    colSpan R.W (mapM (Qq := R.Qq) V) = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) := by
  have h := colSpan_unimod (1 : Matrix (Fin k) (Fin k) R.Qq) V hV
  rwa [one_mul] at h

private theorem colSpan_map_mulVecLin_eq_colSpan_mul (M g : Matrix (Fin k) (Fin k) R.Qq) :
    (colSpan R.W g).map ((Matrix.mulVecLin M).restrictScalars R.W) = colSpan R.W (M * g) := by
  rw [colSpan, colSpan, Submodule.map_span, ← Set.range_comp]
  congr 1

private theorem isEdge_map_mulVecLin_of_isUnit_det (M : Matrix (Fin k) (Fin k) R.Qq) (hM : IsUnit M.det) (e : Edge R.W R.Qq k)
    (he : IsEdge p n' 1 e) :
    IsEdge p n' 1 (⟨e.src.map ((Matrix.mulVecLin M).restrictScalars R.W),
      e.tgt.map ((Matrix.mulVecLin M).restrictScalars R.W)⟩ : Edge R.W R.Qq k) := by
  obtain ⟨⟨g1, hg1, hs⟩, ⟨g2, hg2, ht⟩, hle, hpm, hcard⟩ := he
  set f := (Matrix.mulVecLin M).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f := by
    have h := (Matrix.mulVec_injective_iff_isUnit (A := M)).2 ((Matrix.isUnit_iff_isUnit_det M).2 hM)
    exact h
  refine ⟨⟨M * g1, by rw [Matrix.det_mul]; exact hM.mul hg1, by rw [hs]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g1⟩,
    ⟨M * g2, by rw [Matrix.det_mul]; exact hM.mul hg2, by rw [ht]; exact colSpan_map_mulVecLin_eq_colSpan_mul R M g2⟩,
    Submodule.map_mono hle, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(p : R.W) • y, hpm y hy, map_smul f _ y⟩
  · rw [← hcard]
    let e0 := Submodule.equivMapOfInjective f hfinj e.tgt
    have hPQ : (Submodule.comap e.tgt.subtype e.src).map (e0 : e.tgt →ₗ[R.W] _) =
        Submodule.comap (e.tgt.map f).subtype (e.src.map f) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.1, hy, rfl⟩
      · intro hz
        obtain ⟨y, hys, hyz⟩ := hz
        refine ⟨⟨y, hle hys⟩, hys, Subtype.ext ?_⟩
        exact hyz
    exact (Nat.card_congr (Submodule.Quotient.equiv _ _ e0 hPQ).toEquiv).symm

private theorem natCast_p_ne_zero_Qq (j : Fin k) : (p : R.Qq) ≠ 0 := by
  intro h0
  obtain ⟨g, hg, hgeq⟩ := (baseEdge R j).1
  have hker : colSpan R.W (dj j (p : R.Qq)) ≤
      LinearMap.ker ((LinearMap.proj j : (Fin k → R.Qq) →ₗ[R.Qq] R.Qq).restrictScalars R.W) := by
    rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    simp [dj, Matrix.diagonal_apply, h0]
  obtain ⟨c, hc⟩ : ∃ c, g j c ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg.ne_zero (Matrix.det_eq_zero_of_row_eq_zero j hall)
  have hmem : (fun i => g i c) ∈ colSpan R.W (dj j (p : R.Qq)) := by
    have hgeq' : colSpan R.W (dj j (p : R.Qq)) = colSpan R.W g := hgeq
    rw [hgeq']
    exact Submodule.subset_span ⟨c, rfl⟩
  have h1 := hker hmem
  simp at h1
  exact hc h1

theorem edgeT (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (mapM V * dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  have h := isEdge_map_mulVecLin_of_isUnit_det R (mapM V) (mapM_det_unit R V hV) _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, colSpan_mapM R V hV] at h
  exact h

theorem edgeS (V : Matrix (Fin k) (Fin k) R.W) (hV : IsUnit V.det) (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq), colSpan R.W (mapM V * dj j (p : R.Qq)⁻¹)⟩ :
      Edge R.W R.Qq k) := by
  have hp := natCast_p_ne_zero_Qq R j
  have hdet : IsUnit (mapM V * dj j (p : R.Qq)⁻¹).det := by
    rw [Matrix.det_mul, dj_det]
    exact (mapM_det_unit R V hV).mul (isUnit_iff_ne_zero.2 (inv_ne_zero hp))
  have h := isEdge_map_mulVecLin_of_isUnit_det R _ hdet _ (baseEdge R j)
  simp only [colSpan_map_mulVecLin_eq_colSpan_mul, mul_one, mul_assoc, dj_mul, inv_mul_cancel₀ hp, dj_one,
    colSpan_mapM R V hV] at h
  exact h

theorem transport (L : Submodule R.W (Fin k → R.Qq)) (hL : IsLattice R.W L) {Ne : ℕ}
    (es : Fin Ne → Edge R.W R.Qq k) (hinj : Function.Injective es) (hes : ∀ i, IsEdge p n' 1 (es i)) :
    ∃ es' : Fin Ne → Edge R.W R.Qq k, Function.Injective es' ∧ (∀ i, IsEdge p n' 1 (es' i)) ∧
      (∀ i, (es i).tgt = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).tgt = L) ∧
      (∀ i, (es i).src = colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) → (es' i).src = L) := by
  obtain ⟨g, hg, rfl⟩ := hL
  set f := (Matrix.mulVecLin g).restrictScalars R.W with hfdef
  have hfinj : Function.Injective f :=
    (Matrix.mulVec_injective_iff_isUnit (A := g)).2 ((Matrix.isUnit_iff_isUnit_det g).2 hg)
  refine ⟨fun i => ⟨(es i).src.map f, (es i).tgt.map f⟩, ?_, fun i => isEdge_map_mulVecLin_of_isUnit_det R g hg _ (hes i), ?_, ?_⟩
  · intro i i' h
    apply hinj
    have h1 : (es i).src.map f = (es i').src.map f := congrArg Edge.src h
    have h2 : (es i).tgt.map f = (es i').tgt.map f := congrArg Edge.tgt h
    have e1 := Submodule.map_injective_of_injective hfinj h1
    have e2 := Submodule.map_injective_of_injective hfinj h2
    cases hi : es i
    cases hi' : es i'
    rw [hi, hi'] at e1 e2
    simp only at e1 e2
    rw [e1, e2]
  · intro i hi
    show (es i).tgt.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]
  · intro i hi
    show (es i).src.map f = _
    rw [hi, colSpan_map_mulVecLin_eq_colSpan_mul, mul_one]

end Tr

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

theorem restLeLat : RestLeLat := by
  intro p n' R m e he s
  obtain ⟨gs, hgs, -, h2, -⟩ := edgeLat_RS R e he
  refine ⟨_, ?_, h2 s⟩
  rw [Matrix.det_mul]
  exact (hgs s).mul (lb_D_det (m + 1) 1 _ (RS.w_ne R))

theorem restTensor : RestTensor := restTensor_of restLeLat

end Formalism.MainNotions.flipOneThree.Pf

end
end
