module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle003
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAlg
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransportAn
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle001

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThK.SplitAsm

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ChrFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E) (X : Chars F E)
    (a a' : ℕ) (v : Pl F) (τ : E →ₐ[F] Fv F v), Chars.IsGood B X a a' →
    (∀ x, ‖(chrW X.α τ x : ℂ)‖ = 1) ∧ (∀ x, ‖(chrW X.β τ x : ℂ)‖ = 1) ∧ chrW X.ν τ = chrW X.α τ / chrW X.β τ ∧
    (∃ e : ℕ, CondLE (unifAt v) e (chrW X.α τ) ∧ CondLE (unifAt v) e (chrW X.β τ)) ∧
    (v ∈ X.T → ¬ GlobalTheory.SplitWeil.IsUnram (chrW X.ν τ)) ∧
    (v ∉ X.T → GlobalTheory.SplitWeil.IsUnram (chrW X.α τ) ∧ GlobalTheory.SplitWeil.IsUnram (chrW X.β τ))

theorem extendOn {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ V)
    (g : V → W) (hg : ∀ x ∈ S, ∀ y ∈ S, ∀ c : ℂ, g (x + c • y) = g x + c • g y) :
    ∃ p : V →ₗ[ℂ] W, ∀ x ∈ S, p x = g x := by
  have h0 : g 0 = 0 := by
    have h1 := hg 0 S.zero_mem 0 S.zero_mem 1
    rw [smul_zero, add_zero, one_smul] at h1
    have h2 : g 0 + g 0 = g 0 + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  let gS : S →ₗ[ℂ] W :=
    { toFun := fun x => g x
      map_add' := fun x y => by
        have h3 := hg x x.2 y y.2 1
        rw [one_smul, one_smul] at h3
        simpa using h3
      map_smul' := fun c x => by
        have h3 := hg 0 S.zero_mem x x.2 c
        rw [zero_add, h0, zero_add] at h3
        simpa using h3 }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend gS
  refine ⟨p, fun x hx => ?_⟩
  have h4 := LinearMap.congr_fun hp ⟨x, hx⟩
  simpa [gS] using h4

theorem mk_p {D M P : Type} [AddCommGroup P] [Module ℂ P] (SD : Submodule ℂ (D → ℂ)) (SM : Submodule ℂ (M → ℂ))
    (ι : (D → ℂ) →ₗ[ℂ] (M → ℂ)) (hι : Set.BijOn ι SD SM) (N : Submodule ℂ P) (f : (M → ℂ) → P)
    (hlin : ∀ Φ ∈ SM, ∀ Φ₁ ∈ SM, ∀ c : ℂ, f (Φ + c • Φ₁) = f Φ + c • f Φ₁) (hmem : ∀ Φ ∈ SM, f Φ ∈ N)
    (hon : ∀ y ∈ N, ∃ Φ ∈ SM, f Φ = y) :
    ∃ p : (D → ℂ) →ₗ[ℂ] N, (∀ φ ∈ SD, (p φ : P) = f (ι φ)) ∧ SD.map p = ⊤ := by
  classical
  let g : (D → ℂ) → N := fun φ => if h : ι φ ∈ SM then ⟨f (ι φ), hmem _ h⟩ else 0
  have hgS : ∀ φ ∈ SD, (g φ : P) = f (ι φ) := by
    intro φ hφ
    show ((if h : ι φ ∈ SM then (⟨f (ι φ), hmem _ h⟩ : N) else 0 : N) : P) = f (ι φ)
    rw [dite_eq_left (show ι φ ∈ SM from hι.mapsTo hφ)]
  obtain ⟨p, hp⟩ := extendOn SD g (by
    intro x hx y hy c
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hgS _ (SD.add_mem hx (SD.smul_mem c hy)), hgS _ hx, hgS _ hy,
      map_add, map_smul]
    exact hlin _ (hι.mapsTo hx) _ (hι.mapsTo hy) c)
  refine ⟨p, fun φ hφ => by rw [hp φ hφ]; exact hgS φ hφ, ?_⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨Φ, hΦ, hfΦ⟩ := hon y.1 y.2
  obtain ⟨φ, hφ, hιφ⟩ := hι.surjOn hΦ
  refine ⟨φ, hφ, ?_⟩
  apply Subtype.ext
  rw [hp φ hφ, hgS φ hφ, hιφ, hfΦ]

end PositivityTheory.ThK.SplitAsm
end
end

section

noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix
open GlobalTheory.WeilM

section Forms

variable {k : Type} [Field k] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}

theorem map_mul_c {a b d : Type} [Fintype b] (A : Matrix a b K) (B : Matrix b d K) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem map_one_c {a : Type} [DecidableEq a] : (1 : Matrix a a K).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem exists_left_inv (hK : IsField K) {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (C : Matrix a b K)
    (h : ∀ t, C *ᵥ t = 0 → t = 0) : ∃ L : Matrix b a K, L * C = 1 := by
  letI := hK.toField
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot'.2 fun t ht => h t ht)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem isLagr_of_free [Invertible (2 : k)] (hK : IsField K) (hc : ∀ x, c (c x) = x) {N m : ℕ} (hN : N = 2 * m)
    {J : Matrix (Fin N) (Fin N) K} (hJ : IsSkewM c J) {Y : Matrix (Fin N) (Fin m) K} (hY : Yᵀ * J * Y.map c = 0)
    (hf : ∀ t, Y *ᵥ t = 0 → t = 0) : IsLagr c J Y := by
  obtain ⟨L, hL⟩ := exists_left_inv hK Y hf
  have cc : ∀ {a b : Type} (A : Matrix a b K), (A.map c).map c = A := fun A => Matrix.ext fun i j => hc _
  have hJ' : (J.map c)ᵀ = -J := Matrix.ext fun i j => hJ.1 i j
  have sk : ∀ {a b : Type} (A : Matrix (Fin N) a K) (B : Matrix (Fin N) b K),
      Bᵀ * J * A.map c = -((Aᵀ * J * B.map c).map c)ᵀ := fun A B => by
    rw [map_mul_c, map_mul_c, cc, Matrix.transpose_mul, Matrix.transpose_mul, hJ', Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin N) (Fin m) K, Yᵀ * J * Z.map c = 1 := ⟨(J⁻¹ * Lᵀ).map c, by
    rw [cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.2, ← Matrix.transpose_mul, hL, Matrix.transpose_one]⟩
  have hZ' : Zᵀ * J * Y.map c = -1 := by rw [sk, hZ, map_one_c, Matrix.transpose_one]
  set S := Zᵀ * J * Z.map c with hS
  have hS' : (S.map c)ᵀ = -S := by rw [hS, neg_eq_iff_eq_neg.2 (sk Z Z)]
  let t : Matrix (Fin m) (Fin m) K := -(⅟(2 : k) • Sᵀ)
  have ht : t.map c = ⅟(2 : k) • S := by
    ext i j
    have : c (S j i) = -S i j := congrFun (congrFun hS' i) j
    simp [t, this]
  have a1 : ∀ A B : Matrix (Fin N) (Fin m) K, (A + B).map c = A.map c + B.map c := fun A B =>
    Matrix.map_add _ (map_add c) _ _
  have e1 : Yᵀ * J * (Z + Y * t).map c = 1 := by
    rw [a1, map_mul_c, Matrix.mul_add, hZ, ← Matrix.mul_assoc, hY, Matrix.zero_mul, add_zero]
  have e2 : (Z + Y * t)ᵀ * J * Y.map c = -1 := by rw [sk, e1, map_one_c, Matrix.transpose_one]
  have e3 : (Z + Y * t)ᵀ * J * (Z + Y * t).map c = 0 := by
    rw [a1, map_mul_c, Matrix.mul_add, ← Matrix.mul_assoc, e2, ht, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.transpose_mul, Matrix.mul_assoc tᵀ, Matrix.mul_assoc tᵀ, hZ, ← hS]
    simp only [t, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul, add_neg_cancel]
  set X := Z + Y * t
  have g : (Matrix.fromCols Y X)ᵀ * J * (Matrix.fromCols Y X).map c = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_map, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hY, e1, e2, e3]
  have g' : ((Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((Matrix.fromCols Y X)ᵀ).map c * J.map c)) * Matrix.fromCols Y X = 1 := by
    have := congrArg (fun M => M.map c) g
    simp only [map_mul_c, cc] at this
    rw [Matrix.mul_assoc, this, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one_c, Matrix.map_neg _ (map_neg c),
      map_one_c, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  exact ⟨hY, X, _, e3, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp; omega))).1 g', g'⟩


end Forms

end PositivityTheory.ThK.PT
end
end

section

noncomputable section

namespace PositivityTheory.ThK

open Matrix GlobalTheory.WeilM SiegelT

theorem siegel_transport : SiegelTransport := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ _ hq hψ _ m n N κ _ JA JB d χ Cy om _ hsk hL hW
  obtain ⟨ξ, hq⟩ := hq
  obtain ⟨hs0, dd, omd, hdd, hs, hrule, hres⟩ := hW
  obtain ⟨γ, s, s', h1, h2, hγ⟩ := exists_gamma hq.invol hsk.1 hsk.2 hL
  have hr := rule_of_conj hs γ s s' h1 h2 hγ hrule
  intro l _ hinv p t hp φ hφ
  by_cases h0 : ∀ φ ∈ SB (κ → k), l φ = 0
  · rw [h0 φ hφ, h0 _ (hs0.pres p φ hφ), mul_zero]
  push Not at h0
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  obtain ⟨gd, hgd⟩ := exists_UG (c := c) (J := dbl JB)
    (g := fromBlocks ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) 0 0 1) (by
      rw [dbl, det_fromBlocks_zero₂₁, det_neg]
      exact hsk.2.mul ((isUnit_one.neg.pow _).mul hsk.2)) (by
      have hp' : ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * JB *
        ((p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map c = JB := p.2
      simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one', fromBlocks_multiply]
      simp [hp'])
  let td : GL (Fin n ⊕ Fin n) K := ⟨fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 1,
    fromBlocks ((t⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) 0 0 1,
    by rw [fromBlocks_multiply, Units.mul_inv]; simp, by rw [fromBlocks_multiply, Units.inv_mul]; simp⟩
  have hdet : Matrix.GeneralLinearGroup.det td = Matrix.GeneralLinearGroup.det t :=
    Units.ext (by
      show (fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)).det = (t : Matrix (Fin n) (Fin n) K).det
      rw [det_fromBlocks_zero₂₁, det_one, mul_one])
  have key := hr (boxL l (conjL l)) (Set.mem_univ _) (fun z Φ hΦ => by
    have e : z * (fromBlocks Cy 0 0 Cy)ᵀ = fromCols (z.toCols₁ * Cyᵀ) (z.toCols₂ * Cyᵀ) := by
      conv_lhs => rw [← fromCols_toCols z]
      rw [fromBlocks_transpose, fromCols_mul_fromBlocks]
      simp
    rw [Darboux.rho, e, hdd]
    exact boxL_inv (norm_psi hψ) (hinv _) (hinv _) hΦ) gd td (by
      rw [hgd]
      show _ = fromBlocks Cy 0 0 Cy * fromBlocks (t : Matrix (Fin n) (Fin n) K) 0 0 (1 : Matrix (Fin n) (Fin n) K)
      rw [fromBlocks_multiply, fromBlocks_multiply]
      simp [hp]) (boxFun φ (star φ₀)) (box_mem hφ (star_mem hφ₀))
  rw [hres p gd hgd φ hφ _ (star_mem hφ₀), hdet] at key
  have b : ∀ φ₁, boxL l (conjL l) (boxFun φ₁ (star φ₀)) = l φ₁ * star (l φ₀) := fun φ₁ => by
    have := boxL_box l (conjL l) φ₁ (star φ₀)
    rw [show conjL l (star φ₀) = star (l φ₀) from congrArg (fun f => star (l f)) (star_star φ₀)] at this
    exact this
  rw [b, b, ← mul_assoc] at key
  exact mul_right_cancel₀ (star_ne_zero.mpr hne) key

end PositivityTheory.ThK
end
end
