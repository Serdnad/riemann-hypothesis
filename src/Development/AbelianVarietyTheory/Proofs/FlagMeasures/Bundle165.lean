module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.AdSat

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem isSatFlag_of_isAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (_hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) :
    IsSatFlag I (lamX I (1, xf)) j S := by
  classical
  obtain ⟨-, -, hΛ, h1, h2, -, hL, hS⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  let p : ∀ i, (Fin I.n → I.E) →ₗ[I.E] (Fin (j i) → I.E) := fun i => ((T' i)ᴴ * I.J).mulVecLin
  have hsw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := fun i k => by
    simp [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc]
  have pT : ∀ i x, p i (T i *ᵥ x) = x := fun i x => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h2 i).1]; simp
  have pT' : ∀ i k x, k ≠ i → p i (T k *ᵥ x) = 0 := fun i k x hk => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h1 k i).2.2 hk]; simp
  have pS : ∀ i (u : ∀ i, Fin (j i) → I.E), p i (∑ k, T k *ᵥ u k) = u i := fun i u => by

    rw [map_sum, Finset.sum_eq_single i (fun k _ hk => pT' i k _ hk) (by simp), pT]
  have hsp : ∀ k z, z ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) →
      z = ∑ i, T i *ᵥ p i z ∧ ∀ i : Fin a, ¬ i.castSucc < k → p i z = 0 := fun k z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, -, hu, rfl⟩ := (hS k z).1 hz
      simp only [pS]
      exact ⟨trivial, hu⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, fun i hi => by rw [map_add (f := _), hx.2 i hi, hy.2 i hi, add_zero]⟩
      simp only [map_add (f := _), mulVec_add, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    | smul c x _ hx =>
      refine ⟨?_, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩
      simp only [map_smul, mulVec_smul, ← Finset.smul_sum]
      rw [← hx.1]
  have hmono : Monotone S := fun k l hkl z hz => by
    obtain ⟨u, hu, hu0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => hu0 i fun h => hi (h.trans_le hkl), rfl⟩
  refine ⟨?_, hmono, fun i => ?_, fun k y => ⟨fun hy => ⟨?_, Submodule.subset_span hy⟩, ?_⟩, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨u, -, hu0, rfl⟩ := (hS 0 z).1 hz
    have : ∀ i, u i = 0 := fun i => hu0 i (by simp)
    simp [this]
  · have hsup : Submodule.span I.E (S i.succ : Set (Fin I.n → I.E)) =
        Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊔ LinearMap.range (T i).mulVecLin := by
      apply le_antisymm
      · refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨u, hu, hu0, rfl⟩ := (hS _ z).1 hz
        have e1 : ∑ k, T k *ᵥ u k = ∑ k, T k *ᵥ Function.update u i 0 k + T i *ᵥ u i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ (fun k => T k *ᵥ Function.update u i 0 k) (Finset.mem_univ i)]
          rw [Finset.sum_congr rfl (s₁ := univ.erase i) (f := fun k => T k *ᵥ Function.update u i 0 k)
            (g := fun k => T k *ᵥ u k)
            (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])]
          simp [add_comm]
        rw [e1]
        refine Submodule.add_mem_sup (Submodule.subset_span ((hS _ _).2 ⟨_, fun k => ?_, fun k hk => ?_, rfl⟩))
          ⟨u i, rfl⟩
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]; exact hu k
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]
            refine hu0 k fun h => hk ?_
            rw [Fin.castSucc_lt_succ_iff] at h
            exact Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne h hki)
      · refine sup_le (Submodule.span_mono (hmono (Fin.castSucc_lt_succ).le)) ?_
        letI : Submodule.IsFullLattice I.E (Λ i) := hΛ i
        rw [LinearMap.range_eq_map, ← Submodule.IsFullLattice.span_eq_top (A := I.E) (M := Λ i), Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine (hS _ _).2 ⟨Pi.single i x, fun k => ?_, fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simpa using hx
          · rw [Pi.single_eq_of_ne hki]; exact zero_mem _
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          exact hk Fin.castSucc_lt_succ
        · rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mulVec_zero]) (by simp)]
          simp
    have hinf : Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊓ LinearMap.range (T i).mulVecLin = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨hz, x, rfl⟩
      have : x = 0 := (pT i x).symm.trans ((hsp _ _ hz).2 i (lt_irrefl _))
      simp [this]
    have hinj : Function.Injective (T i).mulVecLin := fun x y hxy => by
      rw [← pT i x, ← pT i y]; exact congrArg (p i) hxy
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
      (LinearMap.range (T i).mulVecLin)
    rw [hinf, ← hsup, LinearMap.finrank_range_of_inj hinj] at this
    simpa [Formalism.HN.rkK] using this
  · obtain ⟨u, hu, -, rfl⟩ := (hS k y).1 hy
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simp, zero_mem _, ?_⟩
    have : (fun l => e ((0 : Fin I₀.n → I₀.E) l)) = 0 := by ext; simp
    rw [this]
    simp
  · rintro ⟨hy, hy'⟩
    obtain ⟨u, u', y₀, hu, -, -, hz⟩ := (hL y).1 hy
    have hp : ∀ i, p i y = u i := fun i => by
      have a1 : ∀ k, p i (T' k *ᵥ u' k) = 0 := fun k => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h1 i k).2.1]; simp
      have a2 : ∀ x, p i (T₀ *ᵥ x) = 0 := fun x => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h2 i).2.2]; simp

      rw [hz, map_add (f := _), map_add (f := _), pS, a2, map_sum]
      simp [a1]
    obtain ⟨b1, b2⟩ := hsp k y hy'
    exact (hS k y).2 ⟨fun i => p i y, fun i => by simpa only [hp] using hu i, b2, b1⟩
  · intro x hx y hy
    obtain ⟨u, -, -, rfl⟩ := (hS _ x).1 hx
    obtain ⟨v, -, -, rfl⟩ := (hS _ y).1 hy
    rw [hform_eq, star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, (h1 i k).1]
    simp

end GlobalTheory.FlagBase.AdSat
end
end

section

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.RadCov

section Defs

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

def lowers (F : ℕ → Submodule R (Fin n → K)) (c : ℕ) : Submodule R (Matrix (Fin n) (Fin n) K) where
  carrier := {T | ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b}
  zero_mem' := fun b y _ => by simp
  add_mem' := fun {S T} hS hT b y hy => by
    rw [Matrix.add_mulVec]
    exact add_mem (hS b y hy) (hT b y hy)
  smul_mem' := fun r T hT b y hy => by
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (hT b y hy)

theorem mem_lowers {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {T : Matrix (Fin n) (Fin n) K} :
    T ∈ lowers F c ↔ ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b := Iff.rfl

def IsDualFlag [StarRing K] (J : Matrix (Fin n) (Fin n) K) (F : ℕ → Submodule R (Fin n → K)) (m : ℕ) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ b, m ≤ b → F b = F m) ∧
    ∀ b, b ≤ m → ∀ y, y ∈ F (m - b) ↔ y ∈ F m ∧ ∀ x ∈ F b, star x ⬝ᵥ (J *ᵥ y) = 0

def Biorth (r : ℕ → ℕ) (m : ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) K)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) K) : Prop :=
  (∀ b, T' b * T b = 1) ∧ (∀ b b', b ≠ b' → T' b * T b' = 0) ∧ ∑ b ∈ Finset.range m, T b * T' b = 1

theorem lowers_succ_le {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) (c : ℕ) :
    lowers F (c + 1) ≤ lowers F c := by
  intro T hT
  rw [mem_lowers] at hT ⊢
  intro b y hy
  exact hT b y (hF (by omega) hy)

theorem lowers_anti {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) : Antitone (lowers F) :=
  antitone_nat_of_succ_le (lowers_succ_le hF)

theorem lowers_mul {F : ℕ → Submodule R (Fin n → K)} {c c' : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F c') : X * Y ∈ lowers F (c + c' + 1) := by
  rw [mem_lowers] at hX hY ⊢
  intro b y hy
  rw [← Matrix.mulVec_mulVec]
  apply hX b
  apply hY (b + c + 1)
  have e : b + c + 1 + c' + 1 = b + (c + c' + 1) + 1 := by omega
  rw [e]
  exact hy

theorem lowers_mul_zero {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F 0) :
    X * Y ∈ lowers F (c + 1) ∧ Y * X ∈ lowers F (c + 1) := by
  have h1 := lowers_mul hX hY
  have h2 := lowers_mul hY hX
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem lowers_eq_bot {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (h0 : F 0 = ⊥)
    (hm : ∀ b, m ≤ b → F b = F m) (hsp : Submodule.span K (F m : Set (Fin n → K)) = ⊤) :
    lowers F m = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [mem_lowers] at hT
  have hzero : ∀ y ∈ (F m : Set (Fin n → K)), T *ᵥ y = 0 := by
    intro y hy
    have hy' : y ∈ F (0 + m + 1) := by
      rw [hm (0 + m + 1) (by omega)]
      exact hy
    have h := hT 0 y hy'
    rw [h0] at h
    exact (Submodule.mem_bot R).1 h
  have hlin : Matrix.toLin' T = 0 := by
    apply LinearMap.ext_on hsp
    intro y hy
    simpa [Matrix.toLin'_apply] using hzero y hy
  have hT0 : T = 0 := by
    apply Matrix.toLin'.injective
    rw [hlin, map_zero]
  exact (Submodule.mem_bot R).2 hT0

theorem lowers_adj [StarRing K] {J : Matrix (Fin n) (Fin n) K} (hJ : Jᴴ = J)
    {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (hF : IsDualFlag J F m) {c : ℕ}
    {T T' : Matrix (Fin n) (Fin n) K} (hT : T ∈ lowers F c) (hadj : J * T' = Tᴴ * J)
    (htop : ∀ y ∈ F m, T' *ᵥ y ∈ F m) : T' ∈ lowers F c := by
  obtain ⟨hmono, h0, hstab, hdual⟩ := hF
  have hleM : ∀ k, F k ≤ F m := by
    intro k
    rcases le_total k m with h | h
    · exact hmono h
    · exact (hstab k h).le
  rw [mem_lowers] at hT ⊢
  intro b y hy
  have hyM : y ∈ F m := hleM _ hy
  rcases le_total m b with hb | hb
  · rw [hstab b hb]
    exact htop y hyM
  ·
    have key : ∀ x ∈ F (m - b), star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = 0 := by
      intro x hx
      have e : star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = star (T *ᵥ x) ⬝ᵥ (J *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.star_mulVec]
      rw [e]
      rcases le_or_gt (b + c + 1) m with hc | hc
      · have hTx : T *ᵥ x ∈ F (m - (b + c + 1)) := by
          apply hT
          have e' : m - (b + c + 1) + c + 1 = m - b := by omega
          rw [e']
          exact hx
        have hy' : y ∈ F (m - (m - (b + c + 1))) := by
          rw [show m - (m - (b + c + 1)) = b + c + 1 by omega]
          exact hy
        exact ((hdual _ (Nat.sub_le _ _) y).1 hy').2 _ hTx
      ·
        have hTx : T *ᵥ x ∈ F 0 := hT 0 x (hmono (by omega) hx)
        rw [h0] at hTx
        rw [(Submodule.mem_bot R).1 hTx, star_zero, zero_dotProduct]
    have hd := hdual (m - b) (Nat.sub_le _ _) (T' *ᵥ y)
    rw [show m - (m - b) = b by omega] at hd
    exact hd.2 ⟨htop y hyM, key⟩

end Defs

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def locFlag (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun y : Fin n → E => P⁻¹ *ᵥ fun l => φ (y l)) '' (F b : Set _))

def PlaceMatch {ι : Type} (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Function.Bijective (fun v => InfinitePlace.mk (φ v)) ∧
    ∀ v, ((InfinitePlace.mk (φ v)).embedding = φ v ∧ X (InfinitePlace.mk (φ v)) = P v) ∨
      ((InfinitePlace.mk (φ v)).embedding = (starRingEnd ℂ).comp (φ v) ∧
        X (InfinitePlace.mk (φ v)) = (P v).map (starRingEnd ℂ))

def pieceHt [StarRing E] (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) : ℝ :=
  Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F (b + 1)) / Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b)

def covStd (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ℝ :=
  GlobalTheory.FlagBase.covAt E j (GlobalTheory.FlagBase.latAt E j Λ fun _ a b => if a = b then 1 else 0)

end Loc

end GlobalTheory.RadCov
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Sphere

private theorem norm_toLp_eq_sqrt_sum_norm_sq (n : ℕ) (y : Fin (n + 1) → ℂ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin (n + 1)))‖ = Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  simp [EuclideanSpace.norm_eq]

private theorem volume_complex_unit_ball_toReal (n : ℕ) :
    (volume {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1}).toReal =
      Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hset : {y : Fin (n + 1) → ℂ | Real.sqrt (∑ i, ‖y i‖ ^ 2) < 1} =
      {y : Fin (n + 1) → ℂ | ∑ i, ‖y i‖ ^ (2 : ℝ) < 1} := by
    ext y
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    rw [Real.sqrt_lt' one_pos, one_pow]
  rw [hset, Complex.volume_sum_rpow_lt_one (Fin (n + 1)) (by norm_num : (1 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin (n + 1)) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [Fintype.card_fin]; push_cast; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem integral_radial (n : ℕ) (f : ℝ → ℝ) :
    ∫ y : Fin (n + 1) → ℂ, f (Real.sqrt (∑ i, ‖y i‖ ^ 2)) =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * f r := by

  let e := MeasurableEquiv.toLp 2 (Fin (n + 1) → ℂ)
  let μ : Measure (EuclideanSpace ℂ (Fin (n + 1))) := (volume : Measure (Fin (n + 1) → ℂ)).map e
  haveI : μ.IsAddHaarMeasure := by
    have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℂ)).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (n + 1) → ℂ))
    exact h
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * (n + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hball : μ.real (Metric.ball 0 1) = Real.pi ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [Measure.real, MeasurableEquiv.map_apply, ← volume_complex_unit_ball_toReal n]
    congr 2
    ext y
    simp [e, norm_toLp_eq_sqrt_sum_norm_sq]
  have key := integral_fun_norm_addHaar μ f
  rw [integral_map_equiv] at key
  simp only [e, MeasurableEquiv.toLp_apply, norm_toLp_eq_sqrt_sum_norm_sq] at key
  rw [key, hdim, hball, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ball_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y =
      2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) *
        ∫ r in (0 : ℝ)..Real.sqrt t, r ^ (2 * n + 1) * Real.exp (-r ^ 2) := by
  have hq (y : Fin (n + 1) → ℂ) : qEps (allPos (n + 1)) y = ∑ i, ‖y i‖ ^ 2 := by
    simp [qEps, allPos]
  have hmeas : MeasurableSet {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t} := by
    simp only [hq]
    exact measurableSet_le (by fun_prop) measurable_const

  have hind : {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}.indicator gauss =
      fun y => (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))
        (Real.sqrt (∑ i, ‖y i‖ ^ 2)) := by
    funext y
    have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    by_cases hy : ∑ i, ‖y i‖ ^ 2 ≤ t
    · have hy' : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt hy
      rw [Set.indicator_of_mem (by simpa [hq] using hy), Set.indicator_of_mem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∈ Set.Iic (Real.sqrt t) from hy'),
        Real.sq_sqrt hs, gauss]
    · have hy' : ¬ Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ Real.sqrt t := by
        intro h
        exact hy ((Real.sqrt_le_sqrt_iff ht.le).mp h)
      rw [Set.indicator_of_notMem (by simpa [hq] using hy), Set.indicator_of_notMem (show Real.sqrt (∑ i, ‖y i‖ ^ 2) ∉ Set.Iic (Real.sqrt t) from hy')]
  rw [← integral_indicator hmeas, hind,
    integral_radial n ((Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2))),
    intervalIntegral.integral_of_le (Real.sqrt_nonneg t)]
  congr 1
  have hfun : (fun r : ℝ => r ^ (2 * n + 1) *
      (Set.Iic (Real.sqrt t)).indicator (fun r => Real.exp (-r ^ 2)) r) =
      (Set.Iic (Real.sqrt t)).indicator (fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2)) := by
    funext r
    by_cases hr : r ∈ Set.Iic (Real.sqrt t)
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  rw [hfun, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]

theorem gaussDens_sphere (n : ℕ) :
    gaussDens (allPos (n + 1)) 1 = Real.pi ^ (n + 1) * Real.exp (-1) / (n.factorial : ℝ) := by
  set C : ℝ := 2 * Real.pi ^ (n + 1) / (n.factorial : ℝ) with hC
  set h : ℝ → ℝ := fun r => r ^ (2 * n + 1) * Real.exp (-r ^ 2) with hh

  have hF : (fun t : ℝ => ∫ y in {y : Fin (n + 1) → ℂ | qEps (allPos (n + 1)) y ≤ t}, gauss y) =ᶠ[nhds 1]
      fun t => C * ∫ r in (0 : ℝ)..Real.sqrt t, h r := by
    filter_upwards [lt_mem_nhds one_pos] with t ht using ball_integral n ht
  have hcont : Continuous h := by rw [hh]; fun_prop
  have h1 := (hcont.integral_hasStrictDerivAt 0 (Real.sqrt 1)).hasDerivAt
  have h2 := Real.hasDerivAt_sqrt (one_ne_zero : (1 : ℝ) ≠ 0)
  have hd := (h1.comp (1 : ℝ) h2).const_mul C
  rw [gaussDens]
  refine (hF.deriv_eq.trans hd.deriv).trans ?_
  simp only [hh, hC, Real.sqrt_one, one_pow, one_mul]
  field_simp
  try ring

end GlobalTheory.GaussMean.Sphere
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagStabMul

theorem latGroup_mul (I : AutInst) (xf : I.Gf) {x y : I.Ginf} (hx : x ∈ latGroup I xf)
    (hy : y ∈ latGroup I xf) : x * y ∈ latGroup I xf := by
  obtain ⟨γ, hγ, rfl, hk⟩ := hx
  obtain ⟨δ, hδ, rfl, hl⟩ := hy
  refine ⟨γ * δ, (GlobalTheory.RatDiscrete.ratSub I).mul_mem hγ hδ, rfl, ?_⟩
  have h : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
    rw [Prod.snd_mul]; group
  rw [h]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hk hl

theorem flagGroup_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  intro I xf a S x hx y hy
  refine ⟨latGroup_mul I xf hx.1 hy.1, fun v k z hz => ?_⟩
  have h : uMat ((x * y) v) = uMat (x v) * uMat (y v) := rfl
  rw [h, ← Matrix.mulVec_mulVec]
  exact hx.2 v k _ (hy.2 v k z hz)

end GlobalTheory.FlagStabMul
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.hasDerivAt_orbit_and_decay_of_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  first | exact @GlobalTheory.GardingVec.fixed_vector_differentiable | exact GlobalTheory.GardingVec.fixed_vector_differentiable | (intros; apply GlobalTheory.GardingVec.fixed_vector_differentiable <;> assumption)
end
