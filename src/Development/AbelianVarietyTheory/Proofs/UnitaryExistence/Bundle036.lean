module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem exists_pos_nsmul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℕ, 0 < n ∧ n • v ∈ X.Λ := by
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_pos hm hn, ?_⟩
    have : (m * n) • (x + y) = n • m • x + m • n • y := by
      rw [smul_add, smul_smul, smul_smul, mul_comm n m]
    rw [this]
    exact X.Λ.add_mem (nsmul_mem hx _) (nsmul_mem hy _)
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    have hki' : IsIntegral ℤ ((k * k) • c) := by
      rw [mul_smul]; exact hki.smul k
    refine ⟨(k.natAbs * k.natAbs) * m, mul_pos (mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)) hm, ?_⟩
    have h1 := X.Λ.smul_mem (⟨(k * k) • c, hki'⟩ : 𝓞 E) hx
    have h2 : ((k.natAbs * k.natAbs : ℕ) : E) = ((k * k : ℤ) : E) := by
      rw [← Int.natAbs_mul_self, Int.cast_natCast]
    convert h1 using 1
    funext i
    show ((k.natAbs * k.natAbs) * m) • (c * x i) = ((k * k) • c) * (m • x i)
    rw [nsmul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, Nat.cast_mul, h2]
    ring

theorem exists_pos_nsmul_mulVec_mem (X : Data E r) (N : Matrix (Fin r) (Fin r) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ X.Λ, d • (N *ᵥ x) ∈ X.Λ := by
  classical
  obtain ⟨s, hs⟩ := X.Λ_fg
  choose n hn0 hn using fun v => exists_pos_nsmul_mem X (N *ᵥ v)
  refine ⟨∏ v ∈ s, n v, Finset.prod_pos fun v _ => hn0 v, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s n hx, mul_smul]
    exact nsmul_mem (hn x) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact X.Λ.add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact X.Λ.smul_mem c hx

theorem zMatE_nsmul_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (n : ℕ) (v : Fin r → E) :
    FJ.zMatE X e (n • β) *ᵥ v = v + n • ((FJ.zMatE X e β - 1) *ᵥ v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, zMatE_mulVec, zMatE_mulVec, add_sub_cancel_left,
    Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← smul_assoc, Finset.smul_sum]
  simp only [Matrix.smul_apply, smul_mul_assoc]

theorem isSkew_nsmul {β : Matrix (Fin ρ) (Fin ρ) E} (hβ : FJ.IsSkew β) (n : ℕ) :
    FJ.IsSkew (n • β) := by
  intro a b
  have h : cc ((n : E)) = n := by simp [cc]
  rw [Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, cc_mul', h, hβ, mul_neg]

noncomputable def zUnit (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E) : GL (Fin r) E :=
  ⟨FJ.zMatE X cu.e β, FJ.zMatE X cu.e (-β), by rw [← zMatE_add, add_neg_cancel, zMatE_zero],
    by rw [← zMatE_add, neg_add_cancel, zMatE_zero]⟩

theorem zUnit_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    zUnit X cu (β + β') = zUnit X cu β * zUnit X cu β' :=
  Units.ext (zMatE_add X cu β β')

theorem exists_isUStab_zUnit (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) : ∃ d : ℕ, 0 < d ∧ ∀ j : ℕ, IsUStab X.Gm X.Λ (zUnit X cu ((j * d) • β)) := by
  obtain ⟨d, hd, h⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e β - 1)
  obtain ⟨d', hd', h'⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e (-β) - 1)
  refine ⟨d * d', mul_pos hd hd', fun j => ⟨zMatE_unitary X cu _ (isSkew_nsmul hβ _), fun x => ?_⟩⟩
  show x ∈ X.Λ ↔ FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x ∈ X.Λ
  constructor
  · intro hx
    rw [zMatE_nsmul_mulVec, mul_comm d, ← mul_assoc, mul_smul]
    exact X.Λ.add_mem hx (nsmul_mem (h x hx) _)
  · intro hx
    have h1 : FJ.zMatE X cu.e ((j * (d * d')) • -β) *ᵥ (FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x)
        ∈ X.Λ := by
      rw [zMatE_nsmul_mulVec X cu.e (-β), ← mul_assoc, mul_smul (j * d) d' (_ *ᵥ _)]
      rw [← mul_assoc] at hx
      exact X.Λ.add_mem hx (nsmul_mem (h' _ hx) _)
    rwa [Matrix.mulVec_mulVec, ← zMatE_add, smul_neg, neg_add_cancel, zMatE_zero,
      Matrix.one_mulVec] at h1

theorem exists_nsmul_mem_zGam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), FJ.IsSkew β → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
  intro E _ _ _ r ρ X cu β hβ
  obtain ⟨d, hd, h⟩ := exists_isUStab_zUnit X cu β hβ
  obtain ⟨S, hS⟩ := X.Γ_index
  choose s hsS hs using fun j => hS _ (h j)
  have key : ∀ i j, i < j → s i = s j → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
    intro i j hij e
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨(k + 1) * d, mul_pos k.succ_pos hd, isSkew_nsmul hβ _,
      zUnit X cu (((k + 1) * d) • β), ?_, rfl⟩
    have h1 := X.Γ.mul_mem (X.Γ.inv_mem (hs i)) (hs (i + k + 1))
    rw [← e, add_assoc, add_mul, add_smul, zUnit_add, ← mul_assoc (s i)⁻¹, inv_mul_cancel_left] at h1
    exact h1
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun j => (⟨s j, hsS j⟩ : S))
  have e' : s i = s j := congrArg Subtype.val e
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key i j h1 e'
  · exact key j i h1 e'.symm

end GlobalTheory.CuspCentre
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspBasis

open GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem map_cc_mul (A B : Matrix (Fin ρ) (Fin ρ) E) : (A * B).map cc = A.map cc * B.map cc := by
  ext a b
  simp [Matrix.mul_apply, cc_sum', cc_mul']

theorem map_cc_cc (A : Matrix (Fin ρ) (Fin ρ) E) : (A.map cc).map cc = A := by
  ext a b
  simp [cc_cc']

theorem map_cc_one : (1 : Matrix (Fin ρ) (Fin ρ) E).map cc = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h, cc]

theorem isSkew_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsSkew β ↔ β.map cc = -βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_iff (β : Matrix (Fin ρ) (Fin ρ) E) : FJ.IsHermE β ↔ β.map cc = βᵀ :=
  ⟨fun h => by ext a b; exact h a b, fun h a b => congrFun (congrFun h a) b⟩

theorem isHerm_conj (P χ : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsHermE χ) :
    FJ.IsHermE (P * χ * (P.map cc)ᵀ) := by
  rw [isHerm_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem isSkew_conj (P β : Matrix (Fin ρ) (Fin ρ) E) (h : FJ.IsSkew β) :
    FJ.IsSkew (Pᵀ * β * P.map cc) := by
  rw [isSkew_iff] at h ⊢
  rw [map_cc_mul, map_cc_mul, h, Matrix.transpose_map, map_cc_cc]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem comb_change {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (v : Fin ρ → E) :
    ∑ a, v a • e₀ a = ∑ b, (v ᵥ* P) b • e b := by
  simp only [h, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

theorem zMatE_change (X : Data E r) {e₀ e : Fin ρ → Fin r → E} {P : Matrix (Fin ρ) (Fin ρ) E}
    (h : ∀ a, e₀ a = ∑ b, P a b • e b) (β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X e₀ β = FJ.zMatE X e (Pᵀ * β * P.map cc) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [zMatE_mulVec, zMatE_mulVec, comb_change h]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have h1 : (fun b => herm X.Gm v (e₀ b)) = P.map cc *ᵥ fun d => herm X.Gm v (e d) := by
    funext b
    rw [h b, herm_comb_r]
    rfl
  change ((β *ᵥ fun b => herm X.Gm v (e₀ b)) ᵥ* P) c =
    ((Pᵀ * β * P.map cc) *ᵥ fun d => herm X.Gm v (e d)) c
  rw [h1, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}

theorem zGam_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {β : Matrix (Fin ρ) (Fin ρ) E}
    (hβ : β ∈ FJ.zGam X cu₀) : Pᵀ * β * P.map cc ∈ FJ.zGam X cu := by
  obtain ⟨hs, γ, hγ, e⟩ := hβ
  exact ⟨isSkew_conj P β hs, γ, hγ, e.trans (zMatE_change X h β)⟩

theorem lattice_le (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) : cu₀.I ≤ cu.I := by
  refine inf_le_inf_left _ fun x hx => ?_
  have hle : Submodule.span E (Set.range cu₀.e) ≤ Submodule.span E (Set.range cu.e) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [h a]
    exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  exact hle hx

theorem crdI_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {v : Fin ρ → E} (hv : v ∈ FJ.crdI 𝔄 cu₀) :
    v ᵥ* P ∈ FJ.crdI 𝔄 cu := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, e⟩ := hv
    exact Submodule.subset_span ⟨a, ha, x, lattice_le h hx, e.trans (comb_change h v)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.smul_vecMul]; exact Submodule.smul_mem _ _ hx

theorem pair_change (P : Matrix (Fin ρ) (Fin ρ) E) (l x : Fin ρ → E) :
    ∑ i, (P *ᵥ l) i * x i = ∑ i, l i * (x ᵥ* P) i := by
  change (P *ᵥ l) ⬝ᵥ x = l ⬝ᵥ (x ᵥ* P)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem xcFD_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {l : Fin ρ → E} (hl : l ∈ FJ.XcFD 𝔄 cu) :
    P *ᵥ l ∈ FJ.XcFD 𝔄 cu₀ := by
  rw [← SetLike.mem_coe, FJ.xcFD_coe] at hl ⊢
  intro x hx
  rw [pair_change]
  exact hl _ (crdI_change 𝔄 h hx)

theorem dualOE_change (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {u : Fin ρ → E} (hu : u ∈ FJ.dualOE (FJ.XcFD 𝔄 cu₀)) :
    u ᵥ* P ∈ FJ.dualOE (FJ.XcFD 𝔄 cu) := by
  intro l hl
  have h1 := hu _ (xcFD_change 𝔄 h hl)
  have h2 := pair_change P l u
  simp only [mul_comm (u _), mul_comm ((u ᵥ* P) _)] at h1 ⊢
  rwa [← h2]

theorem prE_change (X : Data E r) (P χ β : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.prE X (P * χ * (P.map cc)ᵀ) β = FJ.prE X χ (Pᵀ * β * P.map cc) := by
  have : Matrix.trace ((P * χ * (P.map cc)ᵀ)ᵀ * β) = Matrix.trace (χᵀ * (Pᵀ * β * P.map cc)) := by
    rw [← Matrix.mul_assoc χᵀ, Matrix.trace_mul_comm _ (P.map cc)]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  simp only [FJ.prE, this]

theorem form_eq (χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * χ i k * cc (m k) = u ⬝ᵥ (χ *ᵥ fun k => cc (m k)) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_change (P χ : Matrix (Fin ρ) (Fin ρ) E) (u m : Fin ρ → E) :
    ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) =
      ∑ i, ∑ k, (u ᵥ* P) i * χ i k * cc ((m ᵥ* P) k) := by
  have h1 : (fun k => cc ((m ᵥ* P) k)) = (P.map cc)ᵀ *ᵥ fun k => cc (m k) := by
    funext k
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cc_sum', cc_mul', mul_comm]
  rw [form_eq, form_eq, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem phase_change (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) :
    ∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X (P * χ * (P.map cc)ᵀ) β = n := fun β hβ => by
  rw [prE_change]
  exact hχ _ (zGam_change h hβ)

theorem integral_change (N : ℕ) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b)
    {χ : Matrix (Fin ρ) (Fin ρ) E}
    (hχ : ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu),
      (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) :
    ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀),
      (N : E) * ∑ i, ∑ k, u i * (P * χ * (P.map cc)ᵀ) i k * cc (m k) ∈
        Set.range (algebraMap (𝓞 E) E) := fun u hu m hm => by
  rw [form_change]
  exact hχ _ (dualOE_change 1 h hu) _ (dualOE_change 1 h hm)

theorem basis_inv (hP : IsUnit P.det) (h : ∀ a, cu₀.e a = ∑ b, P a b • cu.e b) (a : Fin ρ) :
    cu.e a = ∑ b, P⁻¹ a b • cu₀.e b := by
  rw [comb_change h (P⁻¹ a)]
  have h1 : P⁻¹ a ᵥ* P = (1 : Matrix (Fin ρ) (Fin ρ) E) a := by
    rw [← Matrix.nonsing_inv_mul P hP]
    rfl
  rw [h1]
  simp [Matrix.one_apply]

theorem conj_inv (hP : IsUnit P.det) (χ : Matrix (Fin ρ) (Fin ρ) E) :
    P * (P⁻¹ * χ * (P⁻¹.map cc)ᵀ) * (P.map cc)ᵀ = χ := by
  have h1 : (P⁻¹.map cc)ᵀ * (P.map cc)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← map_cc_mul, Matrix.mul_nonsing_inv P hP, map_cc_one,
      Matrix.transpose_one]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

theorem expoMatch_of_basis_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ N : ℕ) (X : Data E r) (cu₀ cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E), IsUnit P.det → (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) → (∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))) → ∀ χ, FJ.IsHermE χ → ((∀ β ∈ FJ.zGam X cu₀, ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u ∈ FJ.dualOE (FJ.XcFD 1 cu₀), ∀ m ∈ FJ.dualOE (FJ.XcFD 1 cu₀), (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ r ρ N X cu₀ cu P hP h H χ hχ
  have hQ := basis_inv hP h
  have H' := H _ (isHerm_conj P⁻¹ χ hχ)
  constructor
  · intro hA
    have := integral_change N h (H'.1 (phase_change hQ hA))
    rwa [conj_inv hP] at this
  · intro hB
    have := phase_change h (H'.2 (integral_change N hQ hB))
    rwa [conj_inv hP] at this

end GlobalTheory.CuspBasis
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem zMatE_congr_of_entries (X : Data E r) (N : ℕ) (cu : FJ.CuspFD X ρ)
    (c : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n)
    (hc : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ c b)
    (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : ∀ a b (y : E), (∀ a' ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ c a, β a b / X.ξ0 * y = (N : E) * z) :
    ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, FJ.zMatE X cu.e β *ᵥ v = v + N • w := by
  intro v hv
  choose z hz hz' using fun a b => hβ a b _ (hd v hv b)
  refine ⟨∑ a, (∑ b, -z a b) • cu.e a, (hc _).2 fun a => ?_, ?_⟩
  · exact (c a : Submodule (𝓞 E) E).sum_mem fun b _ => (c a : Submodule (𝓞 E) E).neg_mem (hz a b)
  · rw [zMatE_mulVec, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := hz' a b
    have h0 := X.ξ0_ne
    rw [mul_neg, ← h]
    field_simp

theorem mem_zGam_principal_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  intro E _ _ _ H r ρ X N D φ cu c hΛ hφ hΓ hc β
  have hsd := GlobalTheory.SatDual.pairing_pseudoBasis E H D r (-X.ξ0) X.Gm φ ρ cu.e c
    (by rw [cc_neg', X.ξ0_im]) hφ cu.ind (by rw [hΛ]; exact hc)
  have hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n := by
    intro v hv
    rw [← hΛ] at hv
    obtain ⟨x, rfl⟩ := hv
    exact (hsd fun b => -X.ξ0 * herm X.Gm (φ x) (cu.e b)).1 ⟨x, fun _ => rfl⟩
  have h0 := X.ξ0_ne
  constructor
  · rintro ⟨hs, γ, hγ, e⟩
    refine ⟨hs, fun a b y hy => ?_⟩
    obtain ⟨x, hx⟩ := (hsd (Pi.single b y)).2 (by
      intro b' a' ha'
      by_cases hb : b' = b
      · subst hb
        simpa using hy a' ha'
      · exact ⟨0, by simp [Pi.single_eq_of_ne hb]⟩)
    obtain ⟨w, hw, hw'⟩ := ((hΓ γ).1 hγ).2 (φ x) (hΛ ▸ ⟨x, rfl⟩)
    rw [e, zMatE_mulVec, add_right_inj] at hw'
    have h1 : ∀ a, ∑ b', β a b' * herm X.Gm (φ x) (cu.e b') = -(β a b / X.ξ0 * y) := by
      intro a
      rw [Finset.sum_eq_single b]
      · have h2 := hx b
        rw [Pi.single_eq_same] at h2
        rw [← h2]
        field_simp
      · intro b' _ hb'
        have h2 := hx b'
        rw [Pi.single_eq_of_ne hb', mul_eq_zero, neg_eq_zero] at h2
        rw [h2.resolve_left h0, mul_zero]
      · simp
    simp only [h1] at hw'
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [zero_smul] at hw'
      have h3 := Fintype.linearIndependent_iff.1 cu.ind _ hw' a
      exact ⟨0, FractionalIdeal.zero_mem _, by rw [mul_zero]; exact neg_eq_zero.1 h3⟩
    · have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
      have h3 : ∑ a, ((N : E)⁻¹ * (β a b / X.ξ0 * y)) • cu.e a = -w := by
        have h4 : w = (N : E)⁻¹ • (N • w) := by
          rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hN', one_smul]
        rw [h4, ← hw', Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, ← neg_smul, mul_neg, neg_neg]
      refine ⟨_, (hc _).1 (h3 ▸ X.Λ.neg_mem hw) a, ?_⟩
      rw [mul_inv_cancel_left₀ hN']
  · rintro ⟨hs, hβ⟩
    have h1 := zMatE_congr_of_entries X N cu c hd hc β hβ
    have h2 := zMatE_congr_of_entries X N cu c hd hc (-β) (by
      intro a b y hy
      obtain ⟨z, hz, hz'⟩ := hβ a b y hy
      refine ⟨-z, (c a : Submodule (𝓞 E) E).neg_mem hz, ?_⟩
      rw [Matrix.neg_apply, neg_div, neg_mul, hz', mul_neg])
    have hm : FJ.zMatE X cu.e β * FJ.zMatE X cu.e (-β) = 1 := by
      rw [← zMatE_add, add_neg_cancel, zMatE_zero]
    have hm' : FJ.zMatE X cu.e (-β) * FJ.zMatE X cu.e β = 1 := by
      rw [← zMatE_add, neg_add_cancel, zMatE_zero]
    refine ⟨hs, ⟨_, _, hm, hm'⟩, (hΓ _).2 ⟨⟨zMatE_unitary X cu β hs, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, h1⟩, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := h1 x hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)
    · obtain ⟨w, hw, hw'⟩ := h2 _ hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ at hx
      change FJ.zMatE X cu.e (-β) *ᵥ (FJ.zMatE X cu.e β *ᵥ x) = FJ.zMatE X cu.e β *ᵥ x + _ at hw'
      rw [Matrix.mulVec_mulVec, hm', Matrix.one_mulVec] at hw'
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)

end GlobalTheory.CuspCentre
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.thetaChar_half_differentiable_ne_zero_families : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  first | exact @GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | exact GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero | (intros; apply GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero <;> assumption)
end
