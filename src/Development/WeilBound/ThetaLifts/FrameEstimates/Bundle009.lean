module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle004
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

theorem sq_inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) sq_alg_inj

theorem exists_ratEquiv (hp : IsPair B M χX χW om r s r' s') :
    ∃ e : Matrix (Fin n) (Fin d) E ≃ (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) ((e x).1 i), fun i => algebraMap F (AF F) ((e x).2 i)) := by
  choose y z hyz using hp.good.rat
  have hadd : ∀ a b : Matrix (Fin n) (Fin d) E, incM F (a + b) = incM F a + incM F b := fun a b =>
    Matrix.ext fun i j => map_add (inclR (F := F) (AF F)) _ _
  have hsm : ∀ (c : F) (a : Matrix (Fin n) (Fin d) E), incM F (c • a) = algebraMap F (AF F) c • incM F a := fun c a =>
    Matrix.ext fun i j => by
      change (1 : AF F) ⊗ₜ[F] (c • a i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] a i j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
  let l : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have h := hyz (a + b)
        rw [hadd, map_add (f := _), hyz a, hyz b] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_add _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_add _ _ _).symm
      map_smul' := fun c a => by
        have h := hyz (c • a)
        rw [hsm, map_smul, hyz a] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_mul _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_mul _ _ _).symm }
  have hinj : Function.Injective l := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : incM F a = incM F b := M.co.e.injective (by rw [hyz a, hyz b, h1, h2])
    exact Matrix.ext fun i j => sq_inclR_inj (congrFun (congrFun h3 i) j)
  have h2 : Module.finrank F E = 2 := hp.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdim : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨Equiv.ofBijective l ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩, hyz⟩

theorem theta_mul_le (hS : CoefSum) (hE : CoefEq) (hp : IsPair B M χX χW om r s r' s') (μ : Measure (Fin n × Fin d → AF F))
    (hμ : μ.IsAddHaarMeasure) : ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      ‖theta om Φ₁ g h‖ₑ * ‖theta om Φ₂ g h‖ₑ ≤ ENNReal.ofReal c * ∑' x : Matrix (Fin n) (Fin d) E,
        ‖coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ))‖ₑ := by
  obtain ⟨c, hc, h1⟩ := hS F _ B.ψ hp.base.std μ hμ
  obtain ⟨e, he⟩ := exists_ratEquiv hp
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ g h => ?_⟩
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h)
  refine (h1 _ (hs _ h₁) _ (hs _ h₂)).trans (le_of_eq ?_)
  rw [← e.tsum_eq]
  congr 1
  refine tsum_congr fun x => ?_
  rw [← he x, hE F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂ g h]

theorem sq_maj_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) :
    0 ≤ maj τ C N z := by
  unfold maj sz
  split_ifs
  · positivity
  · exact le_rfl

theorem sq_le_of_coef {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {t : ℝ≥0∞} {S : Set (Matrix (Fin n) (Fin d) E)}
    {u : Matrix (Fin n) (Fin d) E → ℂ} {C : Set (Ten F E n d)} {N : ℕ} {g : UA σ X.J} {h : UA σ W.J}
    (h1 : t * t ≤ ENNReal.ofReal c * ∑' x, ‖u x‖ₑ) (h0 : ∀ x ∉ S, u x = 0)
    (h2 : ∀ x, ‖u x‖ ≤ a * a * maj B.emb C N (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ)) :
    t ^ 2 ≤ ENNReal.ofReal (√c * a) ^ 2 * latSum B.emb C N S g h := by
  rw [sq]
  refine h1.trans ?_
  have e : ∑' x, ‖u x‖ₑ = ∑' x : S, ‖u x.1‖ₑ := by
    refine (tsum_subtype_eq_of_support_subset (f := fun x => ‖u x‖ₑ) fun x hx => ?_).symm
    by_contra hn
    exact hx (by simp [h0 x hn])
  rw [e, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_mul hc.le, mul_assoc, latSum]
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), sq]
  exact ENNReal.ofReal_le_ofReal (h2 x.1)

end

theorem sqAll_of' (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqAll := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ N
  refine ⟨NNReal.mk √c (Real.sqrt_nonneg c) • p, C, (continuous_const.mul hpc : Continuous fun f => √c * p f), hC,
    fun f g h => ?_⟩
  have hm : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  exact sq_le_of_coef hc (apply_nonneg p f) (h1 _ hm _ hm g h) (fun x hx => absurd (Set.mem_univ x) hx) fun x => h2 f f _

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_lam {n r : ℕ} {lam : Fin n → (Fin r → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin r ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    (f : ℝ → ℝ) (t : Fin r → ℝ) :
    ∑ k, f (lam k t) = ∑ i, f (t i) + ∑ i, f (-t i) + ((n : ℝ) - 2 * r) * f 0 := by
  have hinj : Function.Injective (Sum.elim ix iy) :=
    Function.Injective.sumElim ix.injective iy.injective h1
  have := Fintype.sum_of_injective _ hinj (fun i => f (lam (Sum.elim ix iy i) t) - f 0) (fun k => f (lam k t) - f 0)
    (fun k hk => by
      rw [h3 k fun i => ⟨fun h => hk ⟨.inl i, h⟩, fun h => hk ⟨.inr i, h⟩⟩]
      simp) (fun _ => rfl)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h2, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add] at this
  linarith

def l1 {a b : Type} [Fintype a] [Fintype b] (A : Matrix a b ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

theorem weightAbsEntrySum_nonneg {a b : Type} [Fintype a] [Fintype b] (A : Matrix a b ℂ) : 0 ≤ l1 A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem intMvPolynomialCoeffAbsSum_mul_le {a b c : Type} [Fintype a] [Fintype b] [Fintype c] (A : Matrix a b ℂ) (B : Matrix b c ℂ) :
    l1 (A * B) ≤ l1 A * l1 B := by
  unfold l1
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ :=
        Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul_le _ _))
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ k, ‖A i k‖ * ∑ k, ∑ j, ‖B k j‖ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem sz_nonneg {n d : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : Ten F E n d) : 0 ≤ sz τ z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem sz_mul_le {n d : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w) (P : Ten F E n n) (Q : Ten F E d d) (z : Ten F E n d) :
    sz τ (P * z * Q) ≤ sz τ P * sz τ Q * sz τ z := by
  have e : ∀ {a b : ℕ} (y : Ten F E a b), sz τ y = ∑ w, l1 (y.map (piInf (τ w))) := fun _ => rfl
  have le : ∀ {a b : ℕ} (y : Ten F E a b) w, l1 (y.map (piInf (τ w))) ≤ sz τ y := fun y w =>
    Finset.single_le_sum (f := fun w => l1 (y.map (piInf (τ w)))) (fun _ _ => weightAbsEntrySum_nonneg _) (Finset.mem_univ w)
  rw [e (P * z * Q), e z, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Matrix.map_mul, Matrix.map_mul]
  refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ?_
  have h1 := intMvPolynomialCoeffAbsSum_mul_le (P.map (piInf (τ w))) (z.map (piInf (τ w)))
  calc _ ≤ sz τ P * l1 (z.map (piInf (τ w))) * sz τ Q :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le P w) (weightAbsEntrySum_nonneg _))) (le Q w) (weightAbsEntrySum_nonneg _)
          (mul_nonneg (sz_nonneg _ _) (weightAbsEntrySum_nonneg _))
    _ = _ := by ring

omit [NumberField E] in
theorem incM_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    incM F (A * B) = incM F A * incM F B := Matrix.map_mul

omit [NumberField E] in
theorem incM_one {a : ℕ} : incM F (1 : Matrix (Fin a) (Fin a) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

omit [NumberField E] in
theorem inv_mul_tor {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {fr : Frame σ J} (hfr : fr.IsGood) {b : GL (Fin n) E}
    {lam : Fin n → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ}
    (hb : ∀ t, mat (fr.a t) * incM F b.1 =
      incM F b.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t))) (s : Fin fr.r → ℝ) :
    incM F (b⁻¹).1 * mat (fr.a s)⁻¹ =
      (Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (-lam k s))) * incM F (b⁻¹).1 := by
  have h0 : fr.a 0 = 1 := by
    have := hfr.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (fr.a s)⁻¹ = fr.a (-s) := by
    rw [inv_eq_iff_mul_eq_one, ← hfr.add, add_neg_cancel, h0]
  have h2 := hb (-s)
  simp only [map_neg] at h2
  have h3 : incM F b.1 * incM F (b⁻¹).1 = 1 := by rw [← incM_mul, Units.mul_inv, incM_one]
  have h4 : incM F (b⁻¹).1 * incM F b.1 = 1 := by rw [← incM_mul, Units.inv_mul, incM_one]
  rw [h1]
  calc _ = incM F (b⁻¹).1 * (mat (fr.a (-s)) * incM F b.1) * incM F (b⁻¹).1 := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
    _ = _ := by rw [h2, ← Matrix.mul_assoc, h4, Matrix.one_mul]

theorem diag_coords (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J' : Matrix (Fin d) (Fin d) E} {fr : Frame σ J} {fr' : Frame σ J'} (hfr : fr.IsGood) (hfr' : fr'.IsGood)
    {b : GL (Fin n) E} {lam : Fin n → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ}
    (hb : ∀ t, mat (fr.a t) * incM F b.1 =
      incM F b.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam k t)))
    {b' : GL (Fin d) E} {lam' : Fin d → (Fin fr'.r → ℝ) →ₗ[ℝ] ℝ}
    (hb' : ∀ t, mat (fr'.a t) * incM F b'.1 =
      incM F b'.1 * Matrix.diagonal fun k => algebraMap (AF F) (AE F E) (rId F (lam' k t)))
    {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∃ (m : ℕ) (K : ℝ), 0 < m ∧ 1 ≤ K ∧ ∀ s t (x : Matrix (Fin n) (Fin d) E),
      ((∃ y ∈ C, At (evI F) (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ - y)) →
        ∀ k l, IsIntegral ℤ ((m : E) * ((b⁻¹).1 * x * (b'⁻¹).1ᵀ) k l)) ∧
      ∑ w, ∑ k, ∑ l, Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (((b⁻¹).1 * x * (b'⁻¹).1ᵀ) k l)‖ ≤
        K * sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  set P := incM F (b⁻¹).1 with hP
  set Q := (incM F (b'⁻¹).1)ᵀ with hQ
  have hc : ∀ k l, Continuous fun y : Ten F E n d => (P * y * Q) k l := fun k l =>
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem k l
  obtain ⟨m, hm, h⟩ := denom_AE (isCompact_iUnion fun k => isCompact_iUnion fun l => hC.image (hc k l))
  refine ⟨m, max 1 (sz τ P * sz τ Q), hm, le_max_left _ _, fun s t x => ?_⟩
  set z := mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ with hz
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  have key : ∀ k l, (P * z * Q) k l = algebraMap (AF F) (AE F E) (rId F (-lam k s)) * inclR (F := F) (AF F) (ξ k l) *
      algebraMap (AF F) (AE F E) (rId F (-lam' l t)) := by
    intro k l
    have e1 : P * z * Q = (P * mat (fr.a s)⁻¹) * incM F x * (incM F (b'⁻¹).1 * mat (fr'.a t)⁻¹)ᵀ := by
      simp only [hz, hQ, Matrix.transpose_mul, Matrix.mul_assoc]
    have e2 : incM F ξ = P * incM F x * Q := by
      rw [hξ, incM_mul, incM_mul]; rfl
    rw [e1, hP, inv_mul_tor hfr hb, inv_mul_tor hfr' hb', Matrix.transpose_mul, Matrix.diagonal_transpose, ← hP, ← hQ,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (P * _), ← e2, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    rfl
  constructor
  · rintro ⟨y, hy, hzy⟩ k l
    refine h _ ⟨(P * y * Q) k l, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨l, y, hy, rfl⟩⟩, ?_⟩
    have h1 : uFin F • z = uFin F • y := by
      rw [← sub_eq_zero, ← smul_sub]
      exact hzy _ evI_uFin
    have h2 : uFin F • (P * z * Q) = uFin F • (P * y * Q) := by
      have e : ∀ u : Ten F E n d, uFin F • (P * u * Q) = P * (uFin F • u) * Q := fun u => by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [e, e, h1]
    have h3 := congrFun (congrFun h2 k) l
    rw [Matrix.smul_apply, Matrix.smul_apply, key, mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, smul_smul,
      uFin_mul_rId, uFin_mul_rId] at h3
    exact h3
  · refine le_trans (le_of_eq ?_) ((sz_mul_le τ P Q z).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sz_nonneg _ _)))
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [key, map_mul, map_mul, piInf_rId, piInf_rId, piInf_inclR, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le, neg_add,
      Real.exp_add]
    ring

theorem norm_emb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (φ : E →+* ℂ) :
    ∃ w, ∀ x, ‖φ x‖ = ‖(τ w).1 x‖ := by
  have := h.1
  let w : InfinitePlace F := InfinitePlace.mk (φ.comp (algebraMap F E))
  have hw : φ.comp (algebraMap F E) = w.embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal w))).symm
  refine ⟨w, fun x => ?_⟩
  have e : ∀ t : EmbOver E w, t.1 x = infEmb t (1 ⊗ₜ x) := fun t => by rw [infEmb_tmul, map_one, one_mul]
  rw [e (τ w), show φ x = infEmb (⟨φ, hw⟩ : EmbOver E w) (1 ⊗ₜ x) from e ⟨φ, hw⟩]
  rcases infEmb_eq_or_conj h (τ w) ⟨φ, hw⟩ with h1 | h1 <;> rw [h1]
  exact RCLike.norm_conj _

end PositivityTheory.ThKEst

end
end
