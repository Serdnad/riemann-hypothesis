module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle058
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.rationalPairingMatrix_inv_mul_self : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), G.Zh⁻¹ * G.Zh = 1 := by
  first | exact @GlobalTheory.HL.GFrames.Zh_inv_mul | exact GlobalTheory.HL.GFrames.Zh_inv_mul | (intros; apply GlobalTheory.HL.GFrames.Zh_inv_mul <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatClose

section
variable {K R : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [CommRing R] [Algebra K R] [TopologicalSpace R]
  (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R)

theorem hf_add_right (x a b : Fin n → R) : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → R) (c : R) (a : Fin n → R) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : Fin n → R) : hf L Hm x 0 = 0 := by simp [hf]
end

theorem form_sub_sum {E : Type} [Field E] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι] (x : Fin n → E) (a : ι → E)
    (v : ι → Fin n → E) (s : Fin n → E) :
    ∑ i, ∑ j, (x - ∑ k, a k • v k) i * Hm i j * s j =
      (∑ i, ∑ j, x i * Hm i j * s j) - ∑ k, a k * ∑ i, ∑ j, v k i * Hm i j * s j := by
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  calc _ = ∑ i, ∑ k, ∑ j, a k * v k i * Hm i j * s j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem bc_add (x y : Fin n → E) : A.bc p (x + y) = A.bc p x + A.bc p y := by
  funext i; simp [Places.bc]
theorem bc_smul (c : E) (x : Fin n → E) : A.bc p (c • x) = (A.loc p).ιE c • A.bc p x := by
  funext i; simp [Places.bc]
theorem bc_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    A.bc p (∑ i ∈ s, x i) = ∑ i ∈ s, A.bc p (x i) := by
  funext j; simp [Places.bc, Finset.sum_apply]
theorem bc_mem_lat (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    A.bc p x ∈ A.lat p Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem step (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
  obtain ⟨oa, hoa⟩ := ha
  choose o ho hoeq using hMx
  have hdiff : h (A.bc p (g j)) - A.bc p (g j) = ∑ i, (Mx - 1) i j • A.bc p (g i) := by
    rw [hg]
    simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨∑ i, (⟨o i j, ho i j⟩ : (A.L p).O) • A.bc p (oa • ((D : 𝓞 E) • g i)),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bc_mem_lat A p Λ (Λ.smul_mem _ (hgΛ i))), ?_⟩
  rw [hdiff, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (oa • ((D : 𝓞 E) • g i) : Fin n → E) = ((D : E) ^ 3 * a) • g i := by
    change (oa : E) • (((D : 𝓞 E) : E) • g i) = _
    have hD : ((D : 𝓞 E) : E) = (D : E) := by simp
    rw [smul_smul, ← hoa, hD]
    congr 1
    ring
  rw [Subring.smul_def, e1, bc_smul, hoeq, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, map_pow, map_intCast]
  ring
end

theorem close_on_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  intro F E _ _ _ _ _ sig A r k G Λ D p h M M' t hΓ hΓD hb hDu hh hM hM' hM1 hM1'
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have key : ∀ l ∈ Λ, ∃ y ∈ A.lat p Λ,
      h (A.bc p l) - A.bc p l = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
    intro l hl
    set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.of fun k l => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)
      with hΓdef
    have hbl : ∀ m, ∃ o : 𝓞 E, (D : E) * ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = o :=
      hb l hl
    choose ob hob using hbl
    choose og hog using hΓD
    let b : Fin (r + 1) ⊕ Fin (r + 1) → E := fun m => ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j)
    let α := Matrix.vecMul b Γ⁻¹
    let w := l - ∑ q, α q • Sum.elim G.f G.f' q
    have hw0 : ∀ m, ∑ i, ∑ j, w i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = 0 := by
      intro m
      rw [form_sub_sum]
      have e : ∑ q, α q * ∑ i, ∑ j, Sum.elim G.f G.f' q i * G.Hm i j * sig (Sum.elim G.f G.f' m j) =
          Matrix.vecMul α Γ m := rfl
      rw [e, Matrix.vecMul_vecMul, hΓ, Matrix.vecMul_one, sub_self]
    have hwloc : ∀ m, hf (A.L p) (G.S p).Hm (A.bc p w) (A.bc p (Sum.elim G.f G.f' m)) = 0 := by
      intro m
      rw [G.Hm_eq p, (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1, hw0, map_zero]
    have hwW : A.bc p w ∈ (G.S p).W0 := by
      have hME : (G.S p).ME = Submodule.span _ (Set.range (Sum.elim (G.S p).f (G.S p).f')) := by
        rw [Frames.ME, FrameStab.spanTo_top, FrameStab.spanTo_top, Set.Sum.elim_range, Submodule.span_union]
      change ∀ y ∈ (G.S p).ME, hf (A.L p) (G.S p).Hm (A.bc p w) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        rcases q with a | a
        · have e := G.f_eq p a
          have h0 := hwloc (Sum.inl a)
          simp only [Sum.elim_inl] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
        · have e := G.f'_eq p a
          have h0 := hwloc (Sum.inr a)
          simp only [Sum.elim_inr] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
      | zero => exact hf_zero_right _ _ _
      | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [hf_smul_right, hx, mul_zero]
    have hhw : h (A.bc p w) = A.bc p w := (FrameStab.stab_eq (A.L p) r k (G.S p)).1 h hh _ hwW
    have hl' : l = w + ∑ q, α q • Sum.elim G.f G.f' q := by simp only [w, sub_add_cancel]
    have hsplit : h (A.bc p l) - A.bc p l = ∑ q, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) := by

      rw [hl', bc_add, bc_sum, map_add (f := _), map_sum, hhw]
      simp only [bc_smul, map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hα : ∀ q, ∃ o : 𝓞 E, (D : E) ^ 2 * α q = o := by
      intro q
      refine ⟨∑ m, ob m * og m q, ?_⟩
      have e : ((∑ m, ob m * og m q : 𝓞 E) : E) = ∑ m, ((ob m : 𝓞 E) : E) * ((og m q : 𝓞 E) : E) := by
        simp
      rw [e]
      simp only [α, Matrix.vecMul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      linear_combination ((D : E) * Γ⁻¹ m q) * hob m + ((ob m : 𝓞 E) : E) * hog m q
    have hper : ∀ q, ∃ z ∈ A.lat p Λ, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) =
          algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
      rintro (j | j)
      · exact step A p Λ D h G.f M t hM hM1 (fun i => hDu (Sum.inl i)) (α (Sum.inl j)) (hα _) j
      · exact step A p Λ D h G.f' M' t hM' hM1' (fun i => hDu (Sum.inr i)) (α (Sum.inr j)) (hα _) j
    choose z hz hze using hper
    exact ⟨∑ q, z q, Submodule.sum_mem _ fun q _ => hz q, by
      rw [hsplit, Finset.smul_sum]; exact Finset.sum_congr rfl fun q _ => hze q⟩
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact key l hl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb' =>
    obtain ⟨y1, hy1, e1⟩ := ha
    obtain ⟨y2, hy2, e2⟩ := hb'
    exact ⟨y1 + y2, add_mem hy1 hy2, by rw [map_add (f := _), smul_add, ← e1, ← e2]; abel⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, map_smul, ← smul_sub, e, smul_comm]

end GlobalTheory.HL.LatClose
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.strong_approximation_additive_quadratic_extension : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → (∀ y : ∀ p, (A.loc p).Fp, {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite → ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o) ∧ (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o) ∧ ∀ (t : E) (y : ∀ p, (A.loc p).Ep), {p | y p ∉ (A.L p).O}.Finite → (∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) → ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.StrongApprox.strong_approx_additive | exact GlobalTheory.HL.StrongApprox.strong_approx_additive | (intros; apply GlobalTheory.HL.StrongApprox.strong_approx_additive <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.numberField_lattice_determined_by_local_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧ {p | A.lat p Λ ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  first | exact @GlobalTheory.HL.PlacesRec.lattice_local | exact GlobalTheory.HL.PlacesRec.lattice_local | (intros; apply GlobalTheory.HL.PlacesRec.lattice_local <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  first | exact @GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | exact GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | (intros; apply GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordGood
open GlobalTheory.HL.Model GlobalTheory.HL.Inhab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem adjugate_int (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : IsIntM L A) :
    IsIntM L A.adjugate := by
  let B : Matrix (Fin n) (Fin n) L.O := fun i j => ⟨A i j, h i j⟩
  have hB : A = L.O.subtype.mapMatrix B := by ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  intro i j
  exact (B.adjugate i j).2

theorem isSD_coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : Good S) :
    IsSD L S.Hm (coordLat S) := by
  obtain ⟨y, hy, hyd⟩ := h.Hm_unit
  refine isSD_stdLat L S.Hm (y • S.Hm.adjugate) h.Hm_int (fun i j => ?_) ?_
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (adjugate_int L _ h.Hm_int i j)
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hyd, one_smul]

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG
  haveI := nontrivial L
  have hsd := isSD_coordLat S hG
  have hmem : ∀ v : S.V, v ∈ coordLat S ↔ ∀ i, v i ∈ L.O := fun v => mem_stdLat L v
  have h1 : ∀ a, S.f a ∈ coordLat S := fun a => (hmem _).2 (hG.f_int a)
  have h2 : ∀ a, S.f' a ∈ coordLat S := fun a => (hmem _).2 (hG.f'_int a)
  have h3 : ∀ a, S.es a ∈ coordLat S := fun a => (hmem _).2 (hG.es_int a)
  have h4 : ∀ a, S.es' a ∈ coordLat S := fun a => (hmem _).2 (hG.es'_int a)
  have hint : ∀ x ∈ coordLat S, ∀ y ∈ coordLat S, hf L S.Hm x y ∈ L.O :=
    fun x hx y hy => (hsd.2 y).2 hy x hx
  have hZ : IsIntM L S.Zh := fun a b => hint _ (h2 b) _ (h1 a)
  have hU : IsUnit (S.D (Fin.last (r + 1))) := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  obtain ⟨-, u, hu, hud⟩ := hG.D_unit _ hU.ne_zero
  have hDet : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  rw [hDet] at hud
  have e1 : S.Zh * (u • S.Zh.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, hud, one_smul]
  have e2 : (u • S.Zh.adjugate) * S.Zh = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hud, one_smul]
  generalize hPdef : u • S.Zh.adjugate = P at e1 e2
  have hP : IsIntM L P := fun i j => by
    rw [← hPdef, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hu (adjugate_int L _ hZ i j)
  haveI : IsNoetherianRing L.O := by
    obtain ⟨-, -, -, hpid, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    infer_instance
  have hfg : (coordLat S).FG := hsd.1.1
  have hh := S.herm.1

  have hc : ∀ a, hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
      if a = Fin.last r then 1 else 0 := fun a => by
    have : hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
        L.cj ((S.Zh * P) a (Fin.last r)) := by

      rw [hf_sum_right, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hf_smul_right, map_mul, mul_comm, hf_symm L hh]
      rfl
    rw [this, e1, Matrix.one_apply]
    split_ifs <;> simp

  have hc' : ∀ b, hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
      if b = Fin.last r then 1 else 0 := fun b => by
    have : hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
        (P * S.Zh) (Fin.last r) b := by
      rw [hf_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hf_smul_right, L.cj_cj]
      rfl
    rw [this, e2, Matrix.one_apply]
    simp [eq_comm]
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.HL.FrameLift.core S S.f S.es S.T S.gram S.dual S.iso (coordLat S) hfg
    hsd.2 h1 h3 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun b => hP _ _) h2) hc
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.HL.FrameLift.core S S.f' S.es' S.T' S.gram' S.dual' S.iso' (coordLat S)
    hfg hsd.2 h2 h4 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun a => cj_int L (hP _ _)) h1) hc'
  refine ⟨(A, B, S.graphOf (coordLat S)), hA, hB, one_mem _, one_mem _, ?_, ?_, fun b => ?_, rfl⟩
  · rw [one_smul]; exact hA'
  · rw [one_smul]; exact hB'
  · refine ⟨S.f' b - S.f b, sub_mem (h2 b) (h1 b), ?_⟩
    simp [Frames.th, hG.gg]

end GlobalTheory.HL.CoordGood
end
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.card_primitiveTuple_extensions_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_extend_prim_one | exact GlobalTheory.GramCount.ncard_extend_prim_one | (intros; apply GlobalTheory.GramCount.ncard_extend_prim_one <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  first | exact @GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | exact GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | (intros; apply GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram <;> assumption)
end

section

open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem residue_rankin_numeric (x : ℝ) (hx : (3 / 2 : ℝ) ≤ x) (f : ℕ) :
    0 < Real.log x ∧
    (2 * Real.pi) ^ f * ((x ^ f) ^ (1 + 1 / Real.log x) *
      ((1 + 1 / Real.log x) / ((1 + 1 / Real.log x) - 1)) ^ (2 * f))
      ≤ (16 * Real.log x) ^ (2 * f) * x ^ f := by
  have hx0 : 0 < x := by linarith
  have hL : (2 / 5 : ℝ) ≤ Real.log x := by
    have h1 := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    have h2 : Real.log (1 + 1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1 h2 ⊢
    linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  refine ⟨hL0, ?_⟩
  have e1 : (1 + 1 / L) / ((1 + 1 / L) - 1) = 1 + L := by
    rw [add_sub_cancel_left]; field_simp; ring
  have e2 : (x ^ f) ^ (1 + 1 / L) = x ^ f * Real.exp 1 ^ f := by
    rw [Real.rpow_add (pow_pos hx0 f), Real.rpow_one, Real.rpow_def_of_pos (pow_pos hx0 f),
      Real.log_pow, ← hLdef, ← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [e1, e2, pow_mul, pow_mul]
  have hb : 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ (16 * L) ^ 2 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_lt_d9
    have hp0 := Real.pi_pos
    have he0 := Real.exp_pos 1
    have h3 : 2 * Real.pi * Real.exp 1 ≤ 18 := by nlinarith
    have h4 : (1 + L) ^ 2 ≤ (7 / 2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ 18 * (7 / 2 * L) ^ 2 :=
          mul_le_mul h3 h4 (by positivity) (by norm_num)
      _ ≤ (16 * L) ^ 2 := by nlinarith [sq_nonneg L]
  have hc := pow_le_pow_left₀ (by positivity) hb f
  calc (2 * Real.pi) ^ f * (x ^ f * Real.exp 1 ^ f * ((1 + L) ^ 2) ^ f)
      = (2 * Real.pi * Real.exp 1 * (1 + L) ^ 2) ^ f * x ^ f := by
        rw [mul_pow (2 * Real.pi * Real.exp 1), mul_pow (2 * Real.pi)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

theorem dedekindZeta_residue_le_log_rootDiscr_pow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤
        (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ hK
  refine ⟨dedekindZeta_residue_pos K, ?_⟩
  obtain ⟨hn, -, hx, hd⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex K hK
  obtain ⟨hL0, hnum⟩ := residue_rankin_numeric _ hx (Formalism.HermitianLatticesTheory.fDeg K)
  set x := 2 * Formalism.HermitianLatticesTheory.vInv K with hxdef
  have hx0 : 0 < x := by linarith
  have hHR := GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' K hK (1 + 1 / Real.log x) (by
    have : 0 < 1 / Real.log x := by positivity
    linarith)
  have hr : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have hc : InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hw : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
    exact_mod_cast Units.torsionOrder_pos K
  rw [hn, hd] at hHR
  rw [dedekindZeta_residue_def, hr, hc, hd, div_le_iff₀ (by positivity)]
  have hp : 0 < (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  have hq : 0 ≤ (16 * Real.log x) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) * x ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  calc (2 : ℝ) ^ 0 * (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * Units.regulator K * (classNumber K : ℝ)
      = (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * ((classNumber K : ℝ) * Units.regulator K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hHR hp.le
    _ ≤ _ := hnum
    _ ≤ _ := by nlinarith

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end
