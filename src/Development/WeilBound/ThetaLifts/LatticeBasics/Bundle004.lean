module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

namespace GlobalTheory.ThK.Dbl.Inert

open MeasureTheory Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

theorem prod_fold (T : ℕ → ℂ) (n : ℕ) :
    (∏ i : Fin (n / 2), T (n - 1 - i) * T i) * (if Odd n then T (n / 2) else 1) = ∏ k ∈ Finset.range n, T k := by
  rw [Fin.prod_univ_eq_prod_range (fun i => T (n - 1 - i) * T i), Finset.prod_mul_distrib]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [if_neg (by simp), show 2 * m / 2 = m by omega, two_mul, Finset.prod_range_add, mul_one, mul_comm,
      ← Finset.prod_range_reflect (fun i => T (m + i))]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))
  · rw [if_pos (by simp), show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 = m + 1 + m by ring, Finset.prod_range_add,
      Finset.prod_range_succ, ← Finset.prod_range_reflect (fun i => T (m + 1 + i)), mul_assoc, mul_comm]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => congrArg T (by have := Finset.mem_range.1 hi; omega))

theorem triv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : Lˣ} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv (ϖ : L) σ q) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] (μ : Measure (GU σ n)) [μ.IsHaarMeasure]
    (hμ : μ (KU σ n) = 1) {s : ℂ} (hs : (n : ℝ) / 2 < s.re) {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n 1 s Φ) :
    Integrable (fun g => Φ (io1 σ n g)) μ ∧ (∫ g, Φ (io1 σ n g) ∂μ) *
      ∏ i ∈ Finset.range n, (1 - (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹ =
      ∏ i ∈ Finset.range n, (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹ := by
  obtain ⟨α, hα, hw⟩ := isZonal_one hU n
  have h2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have lt : ∀ z : ℂ, z.re < 0 → ‖(q : ℂ) ^ z‖ < 1 := fun z hz => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2) hz
  have y0 : varY q ((1 : Lˣ →* ℂˣ) ϖ) s = (q : ℂ) ^ (-(2 * s + 1)) := by simp [varY]
  have y1 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) * α i = (q : ℂ) ^ (-(2 * s + 1) + (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hq]; push_cast; rfl
  have y2 : ∀ i, (q : ℂ) ^ (-(2 * s + 1)) / α i = (q : ℂ) ^ (-(2 * s + 1) - (n - 1 - 2 * (i.val : ℂ))) := fun i => by
    rw [hα, ← Complex.cpow_intCast, ← Complex.cpow_sub _ _ hq]; push_cast; rfl
  obtain ⟨h3, h4, -⟩ := (GlobalTheory.CompanionTheory.InertZetaTop.unramDoublingInert L ϖ σ q n hU μ hμ 1 (fun _ _ => rfl) s Φ hΦ α _ hw).1 (by
    rw [y0]
    refine ⟨lt _ (by simp; linarith), fun i => ?_⟩
    have h5 : 2 * (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (by have := i.2; omega : 2 * i.val + 1 ≤ n)
    have h6 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    rw [← norm_mul, ← norm_inv, ← norm_mul, ← div_eq_mul_inv, y1, y2]
    exact ⟨lt _ (by simp; linarith), lt _ (by simp; linarith)⟩)
  simp only [mul_one] at h3 h4
  refine ⟨h3, ?_⟩
  have e : ∀ z : ℂ, ((q ^ 2 : ℕ) : ℂ) ^ z = (q : ℂ) ^ (2 * z) := fun z => by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]; rfl
  rw [h4, closedForm, y0, ← prod_fold (fun i => (1 - ((q ^ 2 : ℕ) : ℂ) ^ (-(s + n / 2 - i)))⁻¹), mul_assoc (Finset.prod _ _), mul_right_comm,
    ← Finset.prod_range_reflect, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_mul]
  · congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have := i.2
      rw [y1, y2, e, e, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 4 <;> push_cast <;> ring
    · split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [e, show (2 * m + 1) / 2 = m by omega]
        congr 3; push_cast; ring
      · rfl
  · intro i hi
    have hi := Finset.mem_range.1 hi
    have e2 : (-(q : ℂ)) ^ (n - 1 - i) * varX q n ((1 : Lˣ →* ℂˣ) ϖ) s = (-1) ^ (n - (i + 1)) * (q : ℂ) ^ (-(2 * s + (i + 1 : ℕ))) := by
      rw [neg_pow, varX, MonoidHom.one_apply, Units.val_one, one_mul, mul_assoc, ← Complex.cpow_natCast (q : ℂ),
        ← Complex.cpow_add _ _ hq, Nat.cast_sub (by omega), Nat.cast_sub (by omega), show n - 1 - i = n - (i + 1) by omega]
      congr 2; push_cast; ring
    rw [e2]
    refine mul_inv_cancel₀ (sub_ne_zero.2 fun h => ?_)
    have h6 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have := lt (-(2 * s + (i + 1 : ℕ))) (by simp; linarith)
    have h7 := congrArg norm h
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h7
    exact this.ne h7.symm

end GlobalTheory.ThK.Dbl.Inert

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}


variable (σ) in
abbrev G2 (Y : Spc F E n) : Type := UG (cA σ) (dbl (incM F Y.J))

variable {Y : Spc F E n} {A : Spc F E m}

def mat2 (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := x.1.1


variable (σ Y) in
def rat2 : Subgroup (G2 σ Y) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf _

def ht2 (x : G2 σ Y) : ℝ≥0 := heightGL F x.1

def IsPar (p : G2 σ Y) (t : GL (Fin n) (AE F E)) : Prop :=
  mat2 p * diagCols (Fin n) = diagCols (Fin n) * (t : Matrix (Fin n) (Fin n) (AE F E))


variable (σ Y) in
def par2 : Subgroup (G2 σ Y) := Subgroup.closure {p | ∃ t, IsPar p t}

def IsEmb (h h' : UA σ Y.J) (x : G2 σ Y) : Prop := mat2 x = Matrix.fromBlocks (mat h) 0 0 (mat h')

def IsStab2 (B : Base F E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, Commute ((mat2 k).map (piInf (B.emb w))) (Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w))) ∧
    ∀ z z', z ∈ latHat Y → z' ∈ latHat Y → ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)),
      (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inl ∈ latHat Y ∧ (mat2 k' *ᵥ Sum.elim z z') ∘ Sum.inr ∈ latHat Y

structure IsHgt (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ) : Prop where
  iwa : ∀ x : G2 σ Y, ∃ p t, IsPar p t ∧ ∃ k ∈ K, x = p * k
  val : ∀ p t, IsPar p t → ∀ k ∈ K, a (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ)

def flat (a : G2 σ Y → ℝ) (f : G2 σ Y → ℂ) (s₀ s : ℂ) (x : G2 σ Y) : ℂ := (a x : ℂ) ^ (s - s₀) * f x

def eisTerm (f : G2 σ Y → ℂ) (x : G2 σ Y) (q : Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y)))) : ℂ :=
  f ((Quotient.out q).1 * x)

structure IsEisCont (f : ℂ → G2 σ Y → ℂ) (U : Set ℂ) (Ê : ℂ → G2 σ Y → ℂ) : Prop where
  isOpen : IsOpen U
  conn : IsPreconnected U
  disc : ∀ s : ℂ, ∀ᶠ s' in 𝓝[≠] s, s' ∈ U
  half : ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧ ∀ x, HasSum (eisTerm (f s) x) (Ê s x)
  hol : ∀ x, DifferentiableOn ℂ (Ê · x) U
  cont : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) (U ×ˢ Set.univ)
  grow : ∀ s ∈ U, ∃ (ε C : ℝ) (N : ℕ), 0 < ε ∧ ∀ s' ∈ Metric.ball s ε, ∀ x, ‖Ê s' x‖ ≤ C * (ht2 x : ℝ) ^ N

structure IsDbl (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (χ : Chr F E)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop where
  rat : ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : κ → F,
    dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
  weil : IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) (incM F A.J) (dbl (incM F Y.J)) dd χ (diagCols (Fin n)) om
  lin : IsUSplitting (adeleClass F) ψ dd (fun (g : UA σ A.J) x => mat g * x) S
  adm : l ∈ (adeleClass F).adm κ
  kill : ∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F κ, l (dd.rho ψ (z * (diagCols (Fin n))ᵀ) Φ) = l Φ
  fix : ∀ g, ∀ Φ ∈ schA F κ, l (S g Φ) = l Φ
  theta : ∀ Φ ∈ schA F κ, HasSum (fun y : Matrix (Fin m) (Fin n) E =>
    l (dd.rho ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)

def EisValueAt (f : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (val : G2 σ Y → ℂ) : Prop :=
  ∀ x, ∃ e : ℂ → ℂ, MeromorphicOn e Set.univ ∧ (∃ t : ℝ, ∀ s : ℂ, t < s.re → HasSum (eisTerm (f s) x) (e s)) ∧
    AnalyticAt ℂ e s₀ ∧ e s₀ = val x

def SWAniso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) (M : Model σ A Y) r s r' s', B.IsGood σ → 1 ≤ m → 1 ≤ n → A.IsHerm σ B r s →
    min r s = 0 → Y.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ dd om S l, IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) M.co dd → IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a → ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in M.dom, thetaSum F (om x (S g (boxFun Φ₁ (star Φ₂)))) ∂M.μ

structure IsSec (K : Subgroup (G2 σ Y)) (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) : Prop where
  cont : Continuous f
  law : ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (s₁ + n / 2) * f x
  fin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x => f (x * k.1)))

def IsRegAt (Ê : ℂ → G2 σ Y → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → G2 σ Y → ℂ), 0 < r ∧ (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ x, H s x = (s - s₀) ^ k * Ê s x) ∧
    (∀ x, DifferentiableOn ℂ (H · x) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun y : ℂ × G2 σ Y => H y.1 y.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ x, ‖H s x‖ ≤ C * (ht2 x : ℝ) ^ N

def EisContinues : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ b : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ b →
    ∀ K a, IsStab2 (σ := σ) (Y := Y) B K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ U Ê, IsEisCont (flat a f s₁) U Ê ∧ ∀ s₀, ∃ k, IsRegAt Ê s₀ k

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def SchToPol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → min r s = 0 → (∀ Φ ∈ PolData B M, M.I om Φ = 0) → ∀ Φ ∈ schA F _, M.I om Φ = 0

def PolSch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M, Φ ∈ schA F _

def ToSo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 →
    ∀ Φ' ∈ PolData B G.M', ∃ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Ψ = G.M'.I om' Φ'

def LeviEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m

end GlobalTheory.ThK.Dbl

end
end
