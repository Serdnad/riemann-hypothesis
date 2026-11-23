module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory.ThetaReal


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ThetaReal.exists_monomial_matrices : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (_ : Module.Basis (Fin (N ^ g)) A M) (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • _root_.GlobalTheory.ZH.eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ b u s₀ hker hmul hcomm hfix hspan
  subst hN
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩

  let rep : (Fin g ⊕ Fin g → Fin m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j k => ((j k : ℕ) : ZMod (r * m ^ 2))
  let cls : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → Fin m) :=
    fun a k => ⟨(a k).val % m, Nat.mod_lt _ hm⟩
  haveI : NeZero (r * m ^ 2) := ⟨(Nat.mul_pos (by omega) (pow_pos (by omega) 2)).ne'⟩
  have hzero : ((r : ZMod (r * m ^ 2)) * (m : ZMod (r * m ^ 2)) ^ 2) = 0 := by
    exact_mod_cast ZMod.natCast_self (r * m ^ 2)
  have hcls : ∀ a, (r * m) • (a - rep (cls a)) = 0 := fun a => by
    funext k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, nsmul_eq_mul, rep, cls]
    have hx : a k - (((a k).val % m : ℕ) : ZMod (r * m ^ 2)) = (((m * ((a k).val / m) : ℕ) : ZMod (r * m ^ 2))) := by
      rw [sub_eq_iff_eq_add, ← Nat.cast_add, Nat.div_add_mod, ZMod.natCast_zmod_val]
    rw [hx]
    push_cast
    linear_combination (((a k).val / m : ℕ) : ZMod (r * m ^ 2)) * hzero
  have hrep : ∀ j, cls (rep j) = j := fun j => by
    funext k
    apply Fin.ext
    have hlt : (j k : ℕ) < r * m ^ 2 :=
      lt_of_lt_of_le (j k).isLt (by nlinarith)
    simp only [rep, cls, ZMod.val_natCast_of_lt hlt, Nat.mod_eq_of_lt (j k).isLt]
  have hrep0 : rep (cls 0) = 0 := by
    funext k
    simp [rep, cls]
  let s : (Fin g ⊕ Fin g → Fin m) → M := fun j => u (rep j) s₀
  have hA : ∀ a, ∃ c : ℕ, u a s₀ = f (ζ ^ c) • s (cls a) := fun a => by
    obtain ⟨e, he⟩ := hmul (rep (cls a)) (a - rep (cls a))
    have h1 := he s₀
    rw [hfix _ (hcls a), add_sub_cancel] at h1
    refine ⟨e * q, ?_⟩
    show u a s₀ = f (ζ ^ (e * q)) • u (rep (cls a)) s₀
    rw [h1, smul_smul, ← map_mul, ← pow_add]
    have : e * q + e = e * (q + 1) := by ring
    rw [this, pow_mul', hζ, one_pow, map_one, one_smul]
  have hB : ∀ a j, ∃ c : ℕ, u a (s j) = f (ζ ^ c) • s (cls (a + rep j)) := fun a j => by
    obtain ⟨e, he⟩ := hmul a (rep j)
    obtain ⟨c, hc⟩ := hA (a + rep j)
    refine ⟨e + c, ?_⟩
    show u a (u (rep j) s₀) = _
    rw [he, hc, smul_smul, ← map_mul, ← pow_add]
  have hcard : Fintype.card (Fin g ⊕ Fin g → Fin m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
    ring
  have hspan' : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hA a
    show u a s₀ ∈ Submodule.span A (Set.range s)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨cls a, rfl⟩)
  let sB : Module.Basis (Fin g ⊕ Fin g → Fin m) A M := basisOfTopLeSpanOfCardEqFinrank s hspan'
    (by rw [hcard, Module.finrank_eq_card_basis b, Fintype.card_fin])
  have hsB : ⇑sB = s := coe_basisOfTopLeSpanOfCardEqFinrank s hspan' _
  choose c hc using hB
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o :=
    fun a => Matrix.of fun l i => if l = cls (a + rep i) then ζ ^ c a i else 0
  have hsum : ∀ a i, u a (sB i) = ∑ l, f (ρ a l i) • sB l := fun a i => by
    rw [hsB, hc a i]
    simp [ρ, apply_ite f, ite_smul]
  have hmat : ∀ a, LinearMap.toMatrix sB sB (u a) = (ρ a).map f := fun a => by
    ext l i
    rw [LinearMap.toMatrix_apply, hsum a i, Module.Basis.repr_sum_self, Matrix.map_apply]
  have hinj : Function.Injective (fun P : Matrix (Fin g ⊕ Fin g → Fin m) (Fin g ⊕ Fin g → Fin m) o => P.map f) :=
    Matrix.map_injective hf
  refine ⟨Fin g ⊕ Fin g → Fin m, inferInstance, ρ, sB, cls 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsB]
    show u (rep (cls 0)) s₀ = s₀
    rw [hrep0]
    exact hker 0 (smul_zero r) s₀
  · intro a ha
    have hid : u a = LinearMap.id := LinearMap.ext (hker a ha)
    apply hinj
    dsimp only
    rw [← hmat, hid, LinearMap.toMatrix_id]
    convert (Matrix.map_one f (map_zero f) (map_one f)).symm
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
      | (funext x y; exact Subsingleton.elim _ _)
  · intro a a'
    obtain ⟨e, he⟩ := hmul a a'
    refine ⟨e, hinj ?_⟩
    have hcomp : u a ∘ₗ u a' = f (ζ ^ e) • u (a + a') := LinearMap.ext he
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, map_smul, hmat]
    ext l i
    simp [Matrix.map_apply, Matrix.smul_apply]
  · intro a a' ha
    apply hinj
    have hcomp : u a ∘ₗ u a' = u (a + a') := LinearMap.ext (hcomm a a' ha)
    dsimp only
    rw [Matrix.map_mul, ← hmat, ← hmat, ← LinearMap.toMatrix_comp, hcomp, hmat]
  · exact hsum
  · intro i
    refine ⟨rep i, c (rep i) (cls 0), fun l => ?_⟩
    simp only [ρ, Matrix.of_apply]
    rw [hrep0, add_zero, hrep]
    split_ifs <;> rfl

end GlobalTheory.ThetaReal
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

theorem quadraticMap_nonneg_of_tendsto_cofinite {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (q : QuadraticMap ℤ X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hneg
  push_neg at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hneg
  have hinj : Function.Injective (fun n : ℤ => n • x) := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨n, hn⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  nlinarith [mul_self_nonneg (n : ℝ)]

namespace RatModel
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem dotProduct_div_mem_O {J : Type} [Fintype J] {a₀ : M.Z} {v e : J → Ω} {t : Ω}
    (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) : (v ⬝ᵥ e) / t ∈ M.O a₀ := by
  rw [div_eq_mul_inv]
  exact mul_mem (sum_mem fun j _ => mul_mem (hv j) (he j)) ht

theorem val_dotProduct_div {K : Type} [Field K] {y : Sp K ⟶ M.Z} {a₀ : M.Z} (h : ∀ w, y w ⤳ a₀)
    {J : Type} [Fintype J] {v e : J → Ω} {t : Ω} (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀)
    (ht0 : t ≠ 0) (ht' : t ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) :
    M.val y ((v ⬝ᵥ e) / t) = (∑ j, M.val y (v j) * M.val y (e j)) / M.val y t := by
  have h1 : M.val y t * M.val y t⁻¹ = 1 := by
    rw [← val_mul h ht' ht, mul_inv_cancel₀ ht0, val_one]
  have h2 : ∀ s : Finset J, M.val y (∑ j ∈ s, v j * e j) = ∑ j ∈ s, M.val y (v j) * M.val y (e j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [val_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        val_add h (mul_mem (hv a) (he a)) (sum_mem fun j _ => mul_mem (hv j) (he j)),
        val_mul h (hv a) (he a), ih]
  rw [div_eq_mul_inv, div_eq_mul_inv, dotProduct,
    val_mul h (sum_mem fun j _ => mul_mem (hv j) (he j)) ht, h2, eq_inv_of_mul_eq_one_right h1]

end RatModel

namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem Test.norm_pair_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {h : S.Gam} (hh : h ∈ τ.yy.ker) {u : S.J → PadicAlgCl p} (hu : u ∈ τ.E) :
    ‖∑ j, u j * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := hu
    have h1 := τ.le α hα h hh i
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ Real.exp (τ.q α / S.N) * (τ.δ * Real.exp (-(τ.q α / S.N))) :=
          mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = τ.δ := by rw [Real.exp_neg]; field_simp
  | zero => simpa using τ.δ_pos.le
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul c a _ ha =>
    have hc : ‖(c : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 c.2
    have : ∀ j, (c • a) j = (c : PadicAlgCl p) * a j := fun j => rfl
    simp only [this, _root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ 1 * τ.δ := mul_le_mul hc ha (norm_nonneg _) zero_le_one
      _ = τ.δ := _root_.one_mul _

theorem Test.norm_proj_zero_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) (i : S.J) :
    ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  subst hT
  have := τ.le 0 (fun v0 => by
    rw [map_zero]; exact quadraticMap_nonneg_of_tendsto_cofinite τ.q τ.pos _) h hh i
  simpa only [map_zero, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] using this

theorem Test.exists_norm_proj_zero_eq {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) :
    ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = τ.δ := by
  subst hT
  have := τ.unit0 h hh
  simpa only [map_zero] using this

theorem val_pair_div {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {U : Set M.Z}
    (hU : U ⊆ U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U z y)
    {y₀ : S.R →+* PadicAlgCl p} (hat : S.At M y y₀) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U)
    (h : S.Gam) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) :
    M.val (gPt p ≫ y) ((v ⬝ᵥ S.ev h) / S.th x₀) =
      (∑ j, M.val (gPt p ≫ y) (v j) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) / M.val (gPt p ≫ y) (S.th x₀) := by
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hζ : (gPt p ≫ y) w ∈ U := hc.2 ⟨w, rfl⟩
  have hs := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (gPt p ≫ y) w)
  rw [RatModel.val_dotProduct_div hs (fun j => RatModel.ringOn_le_O hζ (hv j))
    (fun j => RatModel.ringOn_le_O (hU hζ) (hO.le (S.ev_mem h j))) hx
    (RatModel.ringOn_le_O (hU hζ) (hO.le (S.th_mem x₀)))
    (RatModel.ringOn_le_O (hU hζ) (hO.th_unit x₀ hx))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hat]

end ThetaSys

theorem coord_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧ ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧ S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ := by
  intro o Ω _ _ _ _ S M U₀ EE hO hLL hT hsup hstr hEE
  have closed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z, ∀ h ∈ S.HH M z,
      (∀ v ∈ EE.E z, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z) ∧
      ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
        S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O z := by
    intro z hz x₀ hx₀ h hh
    have hx : S.th x₀ ≠ 0 := hx₀.1
    refine ⟨fun v hv => ?_, ?_⟩
    · let V : M.Z.Opens := ⟨⋂ j, {a | v j ∈ M.O a}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
      have hV : (V : Set M.Z).Nonempty := ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => by
        simp only [Set.mem_setOf_eq, M.O_genericPoint]; trivial⟩
      have hvV : ∀ j, v j ∈ M.ringOn ((U₀ ⊓ V : M.Z.Opens) : Set M.Z) := fun j =>
        RatModel.mem_ringOn.2 fun a ha => Set.mem_iInter.1 ha.2 j
      refine (hLL.1 (U₀ ⊓ V) inf_le_left (M.nonempty_inf hO.ne hV) z hz).2 _ ?_ ?_
      · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
          (fun j => RatModel.ringOn_le_O ha (hvV j))
          (fun j => RatModel.ringOn_le_O ha.1 (hO.le (S.ev_mem h j)))
          (RatModel.ringOn_le_O ha.1 (hO.th_unit x₀ hx))
      · intro p _ y hc
        have hc0 : M.Cen U₀ z y := ⟨hc.1, fun a ha => (hc.2 ha).1⟩
        obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc0
        obtain ⟨h1, h2⟩ := hsup z p y y₀ τ hc0 hat
        rw [ThetaSys.val_pair_div hO (fun (a : M.Z) (ha : a ∈ (U₀ ⊓ V : M.Z.Opens)) => ha.1) hc hat hvV h hx, norm_div, (h1 x₀).1 hx₀,
          div_le_one τ.δ_pos]
        refine τ.norm_pair_le (h2 ▸ hh) (u := fun j => M.val (gPt p ≫ y) (v j)) ?_
        rw [← hEE.2 z p y y₀ τ hc0 hat]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have hw : ∀ i j, algebraMap o Ω (S.proj (S.TT M z) 0 j i) ∈ M.ringOn (U₀ : Set M.Z) :=
        fun i j => Subalgebra.algebraMap_mem _ _
      have hval : ∀ i (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p)
          (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ →
          ‖M.val (gPt p ≫ y) (((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀)‖ =
            ‖∑ j, y₀ (algebraMap o S.R (S.proj (S.TT M z) 0 j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ / τ.δ := by
        intro i p _ y y₀ τ hc hat
        rw [ThetaSys.val_pair_div hO subset_rfl hc hat (hw i) h hx, norm_div,
          ((hsup z p y y₀ τ hc hat).1 x₀).1 hx₀]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hat (algebraMap o S.R _)]; rfl
      have hmem : ∀ i, ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
        intro i
        refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
        · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
            (fun j => RatModel.ringOn_le_O ha (hw i j))
            (fun j => RatModel.ringOn_le_O ha (hO.le (S.ev_mem h j)))
            (RatModel.ringOn_le_O ha (hO.th_unit x₀ hx))
        · intro p _ y hc
          obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
          have h2 := (hsup z p y y₀ τ hc hat).2
          rw [hval i p y y₀ τ hc hat, div_le_one τ.δ_pos]
          exact τ.norm_proj_zero_le (by rw [← h2]; rfl) (h2 ▸ hh) i
      obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hz).1
      obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
      have h2 := (hsup z p y y₀ τ hc hat).2
      obtain ⟨i, hi⟩ := τ.exists_norm_proj_zero_eq (T := S.TT M z) (by rw [← h2]; rfl) (h2 ▸ hh)
      have h3 := hval i p y y₀ τ hc hat
      rw [hi, div_self τ.δ_pos.ne', RatModel.norm_val_eq_one_iff hc.1 (hmem i), RatModel.isUnit_O_iff] at h3
      refine ⟨i, fun h0 => h3.1 (by simp only [h0, zero_div]), ?_⟩
      simpa only [inv_div] using h3.2
  intro ξ x₀ hx₀ h hh
  obtain ⟨U, b, hξU, -, hb⟩ := EE.loc ξ
  obtain ⟨x, hxU, hxc, hsp, hI⟩ := hstr.2.2.2 ξ U hξU
  have hH : S.HH M x = S.HH M ξ := by simp only [ThetaSys.HH, hI]
  have hTT : S.TT M x = S.TT M ξ := by simp only [ThetaSys.TT, hH]
  obtain ⟨c1, c2⟩ := closed x hxc x₀ (hI ▸ hx₀) h (hH ▸ hh)
  have hle := RatModel.O_le_of_specializes hsp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hb ξ hξU] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hle (c1 v (by rw [hb x hxU]; exact Submodule.subset_span hv))
    | zero => simp
    | add a c _ _ ha hc => rw [add_dotProduct, add_div]; exact add_mem ha hc
    | smul c a _ ha =>
      have : c • a = (c : Ω) • a := rfl
      rw [this, smul_dotProduct, smul_eq_mul, mul_div_assoc]
      exact mul_mem c.2 ha
  · rw [hTT] at c2
    obtain ⟨i, h1, h2⟩ := c2
    exact ⟨i, h1, hle h2⟩

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_coords_mem {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    [DecidableEq J] (A : Subalgebra o Ω) {b : Matrix J J Ω} (hb : b.det ≠ 0) (u : J → Ω) :
    u ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ A := by
  have hu : IsUnit b.det := isUnit_iff_ne_zero.2 hb
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := by
    intro c
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul u b⁻¹) b = u
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

theorem RatModel.val_vecMul_eq_sum {o Ω J K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J] [Field K]
    {M : RatModel o Ω} {y : Sp K ⟶ M.Z} {z : M.Z} (h : ∀ w, y w ⤳ z) {u : J → Ω} {c : Matrix J J Ω}
    (hu : ∀ j, u j ∈ M.O z) (hc : ∀ j i, c j i ∈ M.O z) (i : J) :
    M.val y (Matrix.vecMul u c i) = ∑ j, M.val y (u j) * M.val y (c j i) := by
  have e := map_sum (RatModel.valHomOf y z h) (fun j => (⟨u j, hu j⟩ * ⟨c j i, hc j i⟩ : M.O z)) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at e
  rw [← e]
  congr 1
  simp [Matrix.vecMul, dotProduct]

theorem sum_mul_mem_of_mem_span {J K : Type} [Fintype J] [Field K] (V : ValuationSubring K) (c : J → K)
    {s : Set (J → K)} (hs : ∀ w ∈ s, ∑ j, w j * c j ∈ V) {w : J → K} (hw : w ∈ Submodule.span V s) :
    ∑ j, w j * c j ∈ V := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hs w hw
  | zero => simp
  | add w w' _ _ hw hw' =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hw hw'
  | smul a w _ hw =>
    have : ∑ j, (a • w) j * c j = (a : K) * ∑ j, w j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [this]
    exact mul_mem a.2 hw

theorem mem_EE_iff_forall_test :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → S.IsEE M U₀ EE → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ v : S.J → Ω, (∀ j, v j ∈ M.ringOn U₀) → (v ∈ EE.E z ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (fun j => M.val (gPt p ≫ y) (v j)) ∈ τ.E) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hEE z hz v hv
  refine ⟨fun h p _ y y₀ τ hc hat => ?_, fun h => ?_⟩
  · rw [← hEE.2 z p y y₀ τ hc hat]
    exact Submodule.subset_span ⟨v, h, rfl⟩
  obtain ⟨W, b, hzW, hb, hE⟩ := EE.loc z
  have hstd : ∀ z' ∈ U₀, ∀ u, u ∈ EE.E z' ↔ ∀ j, u j ∈ M.O z' := fun z' hz' u => by
    rw [hEE.1 z' hz']
    exact RatModel.Lat.mem_const_iff M
  have hrow : ∀ z' ∈ W, ∀ u, u ∈ EE.E z' ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ M.O z' := fun z' hz' u => by
    rw [hE z' hz']
    exact mem_span_rows_iff_coords_mem _ hb u
  have hinv : ∀ z' ∈ U₀ ⊓ W, ∀ j i, b⁻¹ j i ∈ M.O z' := fun z' hz' j i => by
    have h1 := (hrow z' hz'.2 (Pi.single j 1)).1 ((hstd z' hz'.1 _).2 fun k => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]) i
    simpa using h1
  rw [hrow z hzW]
  intro i
  refine (hloc.1 (U₀ ⊓ W) inf_le_left (M.nonempty_inf hO.ne ⟨z, hzW⟩) z hz).2 _ ?_ ?_
  · exact RatModel.mem_ringOn.2 fun z' hz' =>
      (hrow z' hz'.2 v).1 ((hstd z' hz'.1 v).2 fun j => RatModel.mem_ringOn.1 (hv j) z' hz'.1) i
  intro p _ y hc
  have hc₀ : M.Cen U₀ z y := ⟨hc.1, fun w hw => (hc.2 hw).1⟩
  obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := htest z p y hc₀
  have hm := h p y y₀ τ hc₀ hat
  rw [← hEE.2 z p y y₀ τ hc₀ hat] at hm
  obtain ⟨ξ, hξU, hsp, hle⟩ : ∃ ξ ∈ U₀ ⊓ W, (∀ w, (gPt p ≫ y) w ⤳ ξ) ∧ M.O z ≤ M.O ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _),
      RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 _)⟩
  rw [RatModel.val_vecMul_eq_sum hsp (fun j => RatModel.mem_ringOn.1 (hv j) ξ hξU.1) (hinv ξ hξU), ← mem_OO_iff]
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hm
  rintro _ ⟨u, huE, rfl⟩
  have h1 := (hrow z hzW u).1 huE
  have h2 : ∀ j, u j ∈ M.O ξ :=
    (hstd ξ hξU.1 u).1 ((hrow ξ hξU.2 u).2 fun k => hle (h1 k))
  have h3 := hc.norm_val_le_one (h1 i)
  rw [RatModel.val_vecMul_eq_sum hsp h2 (hinv ξ hξU)] at h3
  exact (mem_OO_iff _).2 h3

end GlobalTheory.ZH
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_at_test_of_cen :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) := by
  intro o Ω _ _ _ _ S M U₀ hT hO z p _ y hy
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    hy.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
  exact ⟨y₀, fun _ => rfl, hn, hT p y₀ hn⟩

end GlobalTheory.ZH
end
