module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem det_one_updateCol_eq {K : Type} [Field K] {n : ℕ} (i : Fin n) (c : Fin n → K) :
    ((1 : Matrix (Fin n) (Fin n) K).updateCol i c).det = c i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl

theorem exists_minor_det_ne_zero {K : Type} [Field K] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) K)
    (hY : Y.rank = n) : ∃ f : Fin n ↪ Fin d, (Y.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun j => Yᵀ j)
  have htop : Submodule.span K (Set.range (fun j => Yᵀ j)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    rw [← Matrix.finrank_range_mulVecLin, Matrix.range_mulVecLin] at hY
    exact hY
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((fun j => Yᵀ j) ∘ a)) := by rw [hspan, htop]
  let b := Module.Basis.mk hli hsp
  let e : κ ≃ Fin n := b.indexEquiv (Pi.basisFun K (Fin n))
  let f : Fin n ↪ Fin d := e.symm.toEmbedding.trans ⟨a, ha⟩
  refine ⟨f, ?_⟩
  have hli' : LinearIndependent K (fun i => (Y.submatrix id f)ᵀ i) := by
    have : (fun i => (Y.submatrix id f)ᵀ i) = ((fun j => Yᵀ j) ∘ a) ∘ e.symm := by
      funext i r; rfl
    rw [this]; exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem submatrix_mul_left {K : Type} [Field K] {n d : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin d) K) (g : Fin n ↪ Fin d) :
    (B * Y).submatrix id g = B * Y.submatrix id g := by
  ext r s; simp [Matrix.mul_apply]

theorem exists_GL_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ E : GL (Fin n) k, E.val * Y ∈ unitMinorSet k n d := by
  classical
  obtain ⟨f0, hf0⟩ := exists_minor_det_ne_zero Y hY
  haveI : Nonempty (Fin n ↪ Fin d) := ⟨f0⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (fun g : Fin n ↪ Fin d => valuation k (Y.submatrix id g).det)
  have hAdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    have h1 := hf f0
    simp only [h0, map_zero] at h1
    exact hf0 ((map_eq_zero _).mp (le_antisymm h1 zero_le'))
  have hAu : IsUnit (Y.submatrix id f).det := isUnit_iff_ne_zero.mpr hAdet
  let E : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id f)⁻¹
    (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hAdet)
  have hEv : E.val = (Y.submatrix id f)⁻¹ := rfl
  set Z := E.val * Y with hZ
  have hZf : Z.submatrix id f = 1 := by
    rw [hZ, submatrix_mul_left, hEv, Matrix.nonsing_inv_mul _ hAu]
  have hZg : ∀ g : Fin n ↪ Fin d, valuation k (Z.submatrix id g).det ≤ 1 := by
    intro g
    rw [hZ, submatrix_mul_left, hEv, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr (by simpa using hAdet))]
    exact hf g
  refine ⟨E, fun i j => ?_, f, by rw [hZf, Matrix.det_one, map_one]⟩
  rw [Valuation.mem_integer_iff]
  show valuation k (Z i j) ≤ 1
  by_cases hj : ∃ i', f i' = j
  · obtain ⟨i', rfl⟩ := hj
    have := congrFun (congrFun hZf i) i'
    simp only [Matrix.submatrix_apply, id] at this
    rw [this, Matrix.one_apply]
    split_ifs <;> simp
  · push_neg at hj
    have hsub : Z.submatrix id (f.setValue i j) = (1 : Matrix (Fin n) (Fin n) k).updateCol i (fun r => Z r j) := by
      ext r s
      by_cases hs : s = i
      · subst hs; simp [Function.Embedding.setValue_eq]
      · rw [Matrix.updateCol_ne hs]
        have h2 : f.setValue i j s = f s := by
          simp [Function.Embedding.setValue, hs, hj s]
        simp only [Matrix.submatrix_apply, id, h2]
        exact congrFun (congrFun hZf r) s
    have := hZg (f.setValue i j)
    rwa [hsub, det_one_updateCol_eq] at this

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjugate_integral {n : ℕ} (X : Matrix (Fin n) (Fin n) k) (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, X.adjugate i j ∈ 𝒪[k] := by
  let X' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X = (algebraMap 𝒪[k] k).mapMatrix X' := by ext i j; rfl
  intro i j
  rw [e, ← RingHom.map_adjugate]
  exact (X'.adjugate i j).2

theorem mul_integral {a b c : ℕ} (X : Matrix (Fin a) (Fin b) k) (W : Matrix (Fin b) (Fin c) k)
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hW : ∀ i j, W i j ∈ 𝒪[k]) : ∀ i j, (X * W) i j ∈ 𝒪[k] := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)

theorem integral_of_mul {n d : ℕ} (M : Matrix (Fin n) (Fin n) k) (Z : Matrix (Fin n) (Fin d) k)
    (hZ : Z ∈ unitMinorSet k n d) (hMZ : ∀ i j, (M * Z) i j ∈ 𝒪[k]) : ∀ i j, M i j ∈ 𝒪[k] := by
  obtain ⟨hZi, f, hf⟩ := hZ
  set Zf := Z.submatrix id f with hZf
  have hsub : (M * Z).submatrix id f = M * Zf := by
    ext i j; simp [Zf, Matrix.mul_apply]
  have hdet : Zf.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf; exact zero_ne_one hf
  have hM : M = (M * Z).submatrix id f * Zf⁻¹ := by
    rw [hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  have hZfi : ∀ i j, Zf i j ∈ 𝒪[k] := fun i j => hZi _ _
  have hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)
    rw [Valuation.mem_integer_iff, map_inv₀, hf, inv_one]
  rw [hM]
  exact mul_integral _ _ (fun i j => hMZ _ _) hinv

theorem mem_KO_of_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (hY : Y ∈ unitMinorSet k n d)
    (hEY : E.val * Y ∈ unitMinorSet k n d) : E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  refine (mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  exact hY.1

end GlobalTheory.FullRankCoinv.UnitMinor
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem crossT_ι_eq_zero_of_vanish {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ)
    (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r)
    (hc : p < c) :
    (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  have ht : c + l = t := h
  by_cases hcl : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R (twX E V) a b).inv, comp_zero]
    refine free_ext _ _ fun U y => ?_
    have e1 := evT_crossT V ℓ μ hk α z a b r hr U y
    unfold evT at e1
    refine e1.trans ?_
    have h0 : ev α a _ rfl U (baseS V y) = 0 := by
      rw [ev_def, hα _ _ _ hc, comp_zero]
      exact map_zero (mapHom _ _ (freeGen R _ U (baseS V y)))
    rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).symm
  · exact (biChains_isZero (R := R) (twX E V) c l (by omega)).eq_of_src _ _

end GlobalTheory.PBFc
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc

theorem evT_finsetSum {R : Type} [CommRing R] {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} {ι : Type} (S : Finset ι)
    (γ : ι → Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (∑ j ∈ S, γ j) a b s h U y = ∑ j ∈ S, evT (γ j) a b s h U y := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, evT_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evT_add, ih]

theorem evT_phi : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  intro q E N V B ℓ i z n α a b s h U y
  rw [phi_apply, evT_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evT_crossT]
  have he : Even (2 * ((j : ℕ) : ℤ) * (a : ℤ)) := by
    rw [mul_assoc]; exact even_two_mul _
  rw [Int.negOnePow_even _ he, one_smul]

end GlobalTheory.PBFc

end
end

section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem eqv_cor_mul_col {F : Type} [NormedField F] {ψ : AddChar F ℂ} {m : ℕ} {W : GL (Fin (m + 2)) F → ℂ}
    (hW : Eqv ψ W) (h : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    W (cor h * mir 1 x) = ψ (lr h ⬝ᵥ x) * W (cor h) := by
  change W (mir h 0 * mir 1 x) = _
  rw [mir_mul, hW.apply_mir, mul_one, add_zero]
  rfl

theorem eqv_act {F : Type} [NormedField F] {ψ : AddChar F ℂ} {n : ℕ} {W : GL (Fin n) F → ℂ}
    (hW : Eqv ψ W) (T : GL (Fin n) F →₀ ℂ) : Eqv ψ (act T W) := fun u hu g => by
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u, hW u hu]
  ring

theorem lr_ne_zero {F : Type} [NormedField F] {m : ℕ} (h : GL (Fin (m + 1)) F) : lr h ≠ 0 := fun h0 => by
  have h1 : lr (h * h⁻¹) = 0 := by rw [lr_mul, h0, zero_vecMul]
  rw [mul_inv_cancel] at h1
  have := congrFun h1 (Fin.last m)
  simp [lr] at this

end GlobalTheory.JSW.Cut
end

section

open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
end

section

open Matrix Topology

namespace GlobalTheory.JSW.Cut

theorem cuts_mul_open_subgroup {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ}
    (U : Subgroup (GL (Fin n) F)) (hU : IsOpen (U : Set (GL (Fin n) F))) (X A : Set (GL (Fin n) F))
    (hX : ∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) (h : Cuts ψ (U : Set (GL (Fin n) F)) X A) :
    ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧
      Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  obtain ⟨T, hT⟩ := h
  let U₁ : Subgroup (GL (Fin n) F) :=
    { carrier := {u | u ∈ U ∧ ∀ k ∈ T.support, k⁻¹ * u * k ∈ U}
      one_mem' := ⟨one_mem _, fun k _ => by simpa using one_mem U⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by
        have := mul_mem (ha.2 k hk) (hb.2 k hk)
        simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun k hk => by
        have := inv_mem (ha.2 k hk)
        simpa [mul_assoc] using this⟩ }
  refine ⟨U₁, fun u hu => hu.1, ?_, T, ?_⟩
  · have : (U₁ : Set (GL (Fin n) F)) = (U : Set (GL (Fin n) F)) ∩
        ⋂ k ∈ T.support, (fun u : GL (Fin n) F => k⁻¹ * u * k) ⁻¹' (U : Set (GL (Fin n) F)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [this]
    exact hU.inter (isOpen_biInter_finset fun k _ =>
      hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))
  · rintro f hf hfU g ⟨a, ha, u, hu, rfl⟩
    have h1 : act T f (a * u) = act T f a := by
      unfold act
      refine Finset.sum_congr rfl fun k hk => ?_
      have e : a * u * k = a * k * (k⁻¹ * u * k) := by group
      simp only
      rw [e, hfU _ (hu.2 k hk)]
    rw [h1, hT f hf hfU a ha]
    by_cases hx : a ∈ X
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hX a hx u hu.1), hfU u hu.1]
    · have hx' : a * u ∉ X := fun h' => hx (by simpa using hX _ h' u⁻¹ (inv_mem hu.1))
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

end GlobalTheory.JSW.Cut
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_integral_cball_char_eq_zero :
    ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  intro F _ _ _ _ _ _ _ lam _ ψ _ _ hne
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  have hs' : t ∈ GlobalTheory.SplitWeil.cball s := hs
  have hm : MeasurableSet (GlobalTheory.SplitWeil.cball s) := (GlobalTheory.SplitWeil.isOpen_cball s).measurableSet
  have hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s →
      x + y ∈ GlobalTheory.SplitWeil.cball s := fun x y hx hy => by
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  have hneg : -t ∈ GlobalTheory.SplitWeil.cball s := by
    simpa [GlobalTheory.SplitWeil.cball] using hs'
  have hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam)
    ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t
  have h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ GlobalTheory.SplitWeil.cball s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)

end GlobalTheory.KSp
end
