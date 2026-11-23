module

public import GroundTheory.AutomorphicForms.FiniteLengthSubquotient
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import GroundTheory.AutomorphicForms.FiniteLengthJacquet
public import GroundTheory.AutomorphicForms.FiniteLengthLevi
public import GroundTheory.AutomorphicForms.FiniteLengthPieces
public import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.AutomorphicForms.Bundle009
import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.AutomorphicForms.MacdonaldAlternant
public import GroundTheory.AutomorphicForms.SatakeNormalized
public import GroundTheory.AutomorphicForms.WhittakerGroups
public import GroundTheory.AutomorphicForms.AffineBruhat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem exists_piece_of_isSubquotient_jacquetRep [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (h : IsSubquotient τ (jacquetRep F n δ (parabolicInd F n β σ))) :
    ∃ w : Equiv.Perm (Fin n), ∃ _ : ∀ a b, δ a = δ b ↔ β (w a) = β (w b),
      IsSubquotient τ (indRep (cellLeviSub F β δ w) (normInducing σ δ w)) := by
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  obtain ⟨j, hj⟩ := h.exists_piece V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk
  have hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b := by
    by_contra hne
    have := subsingleton_piece_of_isCuspidal hc hne
    have := hj.subsingleton
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    exact hu (Subsingleton.elim _ _)
  refine ⟨w j, fun a b => ⟨fun hab => ?_, hinc a b⟩, hj⟩
  by_contra hne
  obtain ⟨C, p, hp⟩ := hj
  exact not_surjective_of_isCuspidal_piece hσ hinc ⟨a, b, hab, hne⟩ hτ hτc C p hp

theorem hasFiniteLength_jacquetRep_parabolicInd [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ}
    (hδ : ∃ w' : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w' a) = β (w' b)) :
    HasFiniteLength (jacquetRep F n δ (parabolicInd F n β σ)) := by
  obtain ⟨w', hw'⟩ := hδ
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  refine hasFiniteLength_of_filtration V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk fun j => ?_
  by_cases hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b
  · have := isIrreducible_piece hσ (w j) (blocks_eq_of_imp (w' := w') hinc hw')
    exact hasFiniteLength_of_isIrreducible
  · have := subsingleton_piece_of_isCuspidal hc hinc
    exact hasFiniteLength_of_subsingleton

theorem hasFiniteLength_parabolicInd_of_isCuspidal [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) : HasFiniteLength (parabolicInd F n β σ) := by
  classical

  let ι := {δ : Fin n → Fin n // ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w a) = β (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  have : ∀ δ : ι, LocallyCompactSpace (unipotentRadical F n (dN δ)) := fun δ =>
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine hasFiniteLength_of_coinvariants (isSmooth_parabolicInd σ)
    (fun δ : ι => unipotentRadical F n (dN δ)) (fun δ => exists_compactOpen_unipotentRadical)
    (M := fun δ => levi F n (dN δ)) (fun δ => jacquetRep F n (dN δ) (parabolicInd F n β σ))
    (fun δ m => ⟨m, _, fun v => jacquetRep_mk _ m v⟩) (fun δ => ?_) ?_
  ·
    obtain ⟨w', hw'⟩ := δ.2
    obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := dN δ) σ hσ
    choose Ψ _ hΨk using hΨ
    refine hasFiniteLength_of_filtration V hV h0 hk
      (fun j => indRep (cellLeviSub F β (dN δ) (w j)) (normInducing σ (dN δ) (w j))) Ψ hΨk
      fun j => ?_
    by_cases hinc : ∀ a b, β (w j a) = β (w j b) → dN δ a = dN δ b
    · have hiff := blocks_eq_of_imp (w' := w') hinc fun a b => (hdN δ a b).trans (hw' a b)
      have := isIrreducible_piece hσ (w j) hiff
      exact hasFiniteLength_of_isIrreducible
    · have := subsingleton_piece_of_isCuspidal hc hinc
      exact hasFiniteLength_of_subsingleton
  ·
    intro V' _ _ π _ hπ hsub
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
    have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
    obtain ⟨β', U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
    have hq := surjective_frobeniusParabolic hπ Φ hΦ
    have hsubτ : IsSubquotient τ (jacquetRep F n β' (parabolicInd F n β σ)) :=
      (IsSubquotient.of_surjective _ hq).trans (hsub.jacquetRep (isSmooth_parabolicInd σ) β')
    obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hσ hc hτs hτc hsubτ
    have hrank : ∀ a b, β' a = β' b ↔ (rankFun β' a : ℕ) = rankFun β' b := fun a b =>
      eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff β' i j).symm) a b
    let δ : ι := ⟨rankFun β', w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
    refine ⟨δ, ?_⟩
    have hN : unipotentRadical F n (dN δ) = unipotentRadical F n β' :=
      unipotentRadical_congr (rankFun_lt_iff β')
    rw [hN]
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    obtain ⟨y, hy⟩ := hq u
    exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Parabolic

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem superdiagSum_mem {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → M i j ∈ 𝒪[F]) : Whittaker.superdiagSum M ∈ 𝒪[F] := by
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
  split_ifs with hij
  · exact h i j hij
  · exact Subring.zero_mem _

theorem psiN_conj_eq_one {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) {l : Fin n → ℤ}
    (hl : Antitone l) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    Whittaker.psiN ψ₀ (torusPow F n l * k * torusPow F n (-l)) = 1 := by
  refine hψ₀ _ (superdiagSum_mem fun i j hij => ?_)
  have heq : ((torusPow F n l * k * torusPow F n (-l) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = (GLnLocal.uniformizer F : F) ^ (l i - l j) * k i j := by
    rw [Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, mul_diagonal, diagonal_mul,
      Pi.neg_apply, zpow_sub₀ (uniformizer_ne_zero F), _root_.zpow_neg, div_eq_mul_inv]
    ring
  rw [heq]
  have ht : 0 ≤ l i - l j := by
    have := hl (show i ≤ j from Fin.le_def.2 (by omega))
    linarith
  refine Subring.mul_mem _ ?_ (((mem_integralGL_iff F n).1 hk).1 i j)
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ht
  rw [hm, zpow_natCast]
  exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m

theorem exists_iwasawa_decomp (g : GL (Fin n) F) :
    ∃ p : GL (Fin n) F × GL (Fin n) F, p.1 ∈ unipotent F n ∧ p.2 ∈ integralGL F n ∧
      g = p.1 * torusPow F n (iwasawaExponent F n g) * p.2 := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  exact ⟨(u, k), hu, hk, h⟩

def iwasawaUnip (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.1

def iwasawaInt (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.2

theorem iwasawaUnip_mem (g : GL (Fin n) F) : iwasawaUnip g ∈ unipotent F n :=
  (exists_iwasawa_decomp g).choose_spec.1

theorem iwasawaInt_mem (g : GL (Fin n) F) : iwasawaInt g ∈ integralGL F n :=
  (exists_iwasawa_decomp g).choose_spec.2.1

theorem eq_iwasawa (g : GL (Fin n) F) :
    g = iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g :=
  (exists_iwasawa_decomp g).choose_spec.2.2


variable (ψ₀ : AddChar F ℂ) (z : Fin n → ℂˣ) in
def sphericalWhittaker (g : GL (Fin n) F) : ℂ :=
  if Antitone (iwasawaExponent F n g) then
    Whittaker.psiN ψ₀ (iwasawaUnip g) * halfModulus F (iwasawaExponent F n g) *
      evalAt z (schur (iwasawaExponent F n g))
  else 0

theorem sphericalWhittaker_apply {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {u k : GL (Fin n) F} (hu : u ∈ unipotent F n) (hk : k ∈ integralGL F n)
    (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (u * torusPow F n l * k) =
      if Antitone l then Whittaker.psiN ψ₀ u * halfModulus F l * evalAt z (schur l) else 0 := by
  have hexp : iwasawaExponent F n (u * torusPow F n l * k) = l := iwasawaExponent_eq F n hu hk
  have hu' := iwasawaUnip_mem (u * torusPow F n l * k)
  have hk' := iwasawaInt_mem (u * torusPow F n l * k)
  have heq := eq_iwasawa (u * torusPow F n l * k)
  set u' := iwasawaUnip (u * torusPow F n l * k)
  set k' := iwasawaInt (u * torusPow F n l * k)
  rw [sphericalWhittaker, hexp]
  split_ifs with hl
  swap
  · rfl
  rw [hexp] at heq

  have hv : u⁻¹ * u' = torusPow F n l * (k * k'⁻¹) * torusPow F n (-l) := by
    rw [torusPow_neg]
    have := congrArg (fun g => u⁻¹ * g * k'⁻¹ * (torusPow F n l)⁻¹) heq
    rw [show u⁻¹ * (u * torusPow F n l * k) * k'⁻¹ * (torusPow F n l)⁻¹ =
      torusPow F n l * (k * k'⁻¹) * (torusPow F n l)⁻¹ by group,
      show u⁻¹ * (u' * torusPow F n l * k') * k'⁻¹ * (torusPow F n l)⁻¹ = u⁻¹ * u' by group] at this
    exact this.symm
  have h1 : Whittaker.psiN ψ₀ (u⁻¹ * u') = 1 := by
    rw [hv]
    exact psiN_conj_eq_one hψ₀ hl (mul_mem hk ((integralGL F n).inv_mem hk'))
  have h2 : u' = u * (u⁻¹ * u') := by group
  change Whittaker.psiN ψ₀ u' * halfModulus F l * evalAt z (schur l) = _
  rw [h2, Whittaker.psiN_mul ψ₀ hu ((unipotent F n).mul_mem ((unipotent F n).inv_mem hu) hu'), h1,
    mul_one]

theorem sphericalWhittaker_mul_left {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {v : GL (Fin n) F} (hv : v ∈ unipotent F n) (g : GL (Fin n) F) :
    sphericalWhittaker ψ₀ z (v * g) = Whittaker.psiN ψ₀ v * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, show v * (iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g) =
    (v * iwasawaUnip g) * torusPow F n (iwasawaExponent F n g) * iwasawaInt g by group,
    sphericalWhittaker_apply hψ₀ z ((unipotent F n).mul_mem hv hu) hk,
    sphericalWhittaker_apply hψ₀ z hu hk, Whittaker.psiN_mul ψ₀ hv hu]
  split_ifs <;> ring

theorem sphericalWhittaker_mul_right {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) {k₀ : GL (Fin n) F} (hk₀ : k₀ ∈ integralGL F n) :
    sphericalWhittaker ψ₀ z (g * k₀) = sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, mul_assoc, sphericalWhittaker_apply hψ₀ z hu (mul_mem hk hk₀),
    sphericalWhittaker_apply hψ₀ z hu hk]

theorem sphericalWhittaker_torusPow {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (torusPow F n l) =
      if Antitone l then halfModulus F l * evalAt z (schur l) else 0 := by
  have := sphericalWhittaker_apply hψ₀ z (unipotent F n).one_mem (integralGL F n).one_mem l
  rw [one_mul, mul_one, Whittaker.psiN_one, one_mul] at this
  exact this

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

end Spherical

end GroundTheory.Automorphic
end
end
