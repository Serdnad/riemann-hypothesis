module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.extCont_of :
    ExtCont := by
  intro Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy
  | tmul l m =>
    let b := Module.finBasis F M
    have key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) =
        ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i) := by
      intro g
      rw [LinearMap.baseChange_tmul]
      conv_lhs => rw [← b.sum_repr (a g m)]

      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]
      rfl
    simp_rw [key]
    exact continuous_finsetSum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem splits_transport {Z Y W Z' Y' : Scheme.{0}} {J : Type} {s : Y ⟶ Z} {c : W ⟶ Z} {σ : J → (W ⟶ Y)}
    (y : Y ⟶ Y') [IsIso y] (z : Z ⟶ Z') [IsIso z] (s' : Y' ⟶ Z') (hy : y ≫ s' = s ≫ z)
    (h : GlobalTheory.GalV.Splits s c σ) : GlobalTheory.GalV.Splits s' (c ≫ z) (fun j => σ j ≫ y) := by
  obtain ⟨h0, hi⟩ := h
  have h1 : ∀ j, (σ j ≫ y) ≫ s' = c ≫ z := fun j => by
    rw [Category.assoc, hy, ← Category.assoc, h0 j]
  refine ⟨h1, ?_⟩
  have ec : (pullback.fst s c ≫ y) ≫ s' = pullback.snd s c ≫ c ≫ z := by
    rw [Category.assoc, hy, ← Category.assoc, pullback.condition, Category.assoc]
  have ec' : (pullback.fst s' (c ≫ z) ≫ inv y) ≫ s = pullback.snd s' (c ≫ z) ≫ c := by
    rw [← cancel_mono z, Category.assoc, Category.assoc, Category.assoc, ← hy, IsIso.inv_hom_id_assoc,
      pullback.condition]
  let e : pullback s c ⟶ pullback s' (c ≫ z) := pullback.lift _ _ ec
  let e' : pullback s' (c ≫ z) ⟶ pullback s c := pullback.lift _ _ ec'
  have e1 : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y := pullback.lift_fst _ _ _
  have e2 : e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have e1' : e' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv y := pullback.lift_fst _ _ _
  have e2' : e' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have he : IsIso e := by
    refine ⟨e', pullback.hom_ext ?_ ?_, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, e1', ← Category.assoc, e1, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2', e2, Category.id_comp]
    · rw [Category.assoc, e1, ← Category.assoc, e1', Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, e2, e2', Category.id_comp]
  have key : (Sigma.desc (fun j => pullback.lift (σ j ≫ y) (𝟙 W) (by rw [h1 j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s' (c ≫ z)) =
      Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h0 j, Category.id_comp])) ≫ e := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, e1, pullback.lift_fst_assoc]
    · rw [pullback.lift_snd, Category.assoc, e2, pullback.lift_snd]
  rw [key]
  exact IsIso.comp_isIso

private theorem galMap_geomMap {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p)
    (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ geomMap Ω p u hu = geomMap Ω p u hu ≫ galMap Ω q σ := by
  apply pullback.hom_ext
  · simp only [geomMap, Category.assoc, pullback.lift_fst, galMap_fst, galMap_fst_assoc]
  · simp only [geomMap, Category.assoc, pullback.lift_snd, galMap_snd, galMap_snd_assoc, pullback.lift_snd_assoc]

private theorem galMap_inv_comp {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ⁻¹ ≫ galMap Ω p σ = 𝟙 _ := by
  rw [← galMap_mul, inv_mul_cancel, galMap_one]

private theorem galMap_isIso {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ : Ω ≃ₐ[k] Ω) : IsIso (galMap Ω p σ) :=
  ⟨galMap Ω p σ⁻¹, by rw [← galMap_mul, mul_inv_cancel, galMap_one], galMap_inv_comp Ω p σ⟩

theorem UpperTheory.Gal.Int.Geo.opConj_of :
    OpConj := by
  rintro l _ k _ H Ω _ _ g T σ ⟨W, c, G, _, _, a, J, _, σj, ⟨hf, he, hsu, h1, hm, hc⟩, hS, hT⟩
  have hz' : IsIso (galMap Ω H.q σ⁻¹) := galMap_isIso Ω H.q σ⁻¹
  have hy' : IsIso (galMap Ω (H.s g ≫ H.q) σ⁻¹) := galMap_isIso Ω _ σ⁻¹
  have hs : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.sΩ Ω g = H.sΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.s g) rfl σ⁻¹
  have ht : galMap Ω (H.s g ≫ H.q) σ⁻¹ ≫ H.tΩ Ω g = H.tΩ Ω g ≫ galMap Ω H.q σ⁻¹ :=
    galMap_geomMap Ω (H.t g) (H.comm g) σ⁻¹
  refine ⟨W, c ≫ galMap Ω H.q σ⁻¹, G, inferInstance, inferInstance, a, J, inferInstance,
    fun j => σj j ≫ galMap Ω (H.s g ≫ H.q) σ⁻¹, ⟨inferInstance, inferInstance, inferInstance, h1, hm, ?_⟩,
    splits_transport _ _ _ hs hS, fun x => ?_⟩
  · simpa only [Category.comp_id] using
      splits_transport (𝟙 W) (galMap Ω H.q σ⁻¹) (c ≫ galMap Ω H.q σ⁻¹) (Category.id_comp _) hc
  · have hL : ∀ v, GlobalTheory.GalV.pullTot l (sch.map (c ≫ galMap Ω H.q σ⁻¹)) (galTot l Ω H.q σ v) =
        GlobalTheory.GalV.pullTot l (sch.map c) v := fun v => by
      unfold galTot
      rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc,
        galMap_inv_comp, Category.comp_id]
    simp only [LinearMap.comp_apply]
    rw [hL, hT]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold galTot
    rw [← LinearMap.comp_apply, ← GlobalTheory.GalV.pullTot_comp, ← Functor.map_comp, Category.assoc, Category.assoc, ht]
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem inv_top {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊤ : Submodule k (Fin d → k)) := by
  intro g v _
  exact Submodule.mem_top

private theorem inv_bot {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [Submodule.mem_bot] at hv ⊢
  subst hv
  exact Matrix.mulVec_zero _

private theorem flag_step {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k)
    (W : Submodule k (Fin d → k)) (hW : IsInv ρ W) :
    ∃ W' : Submodule k (Fin d → k), IsInv ρ W' ∧ W ≤ W' ∧ (W ≠ ⊤ → W < W') ∧
      ∀ U, IsInv ρ U → W ≤ U → U ≤ W' → U = W ∨ U = W' := by
  by_cases h : W = ⊤
  · subst h
    exact ⟨⊤, hW, le_rfl, fun h => (h rfl).elim, fun U _ h1 h2 => Or.inl (le_antisymm h2 h1)⟩
  · have hne : {U : Submodule k (Fin d → k) | IsInv ρ U ∧ W < U}.Nonempty :=
      ⟨⊤, inv_top ρ, lt_top_iff_ne_top.2 h⟩
    obtain ⟨M, ⟨hMi, hMl⟩, hmin⟩ :=
      (wellFounded_lt (α := Submodule k (Fin d → k))).has_min _ hne
    refine ⟨M, hMi, hMl.le, fun _ => hMl, fun U hU h1 h2 => ?_⟩
    rcases eq_or_lt_of_le h1 with e | l
    · exact Or.inl e.symm
    · rcases eq_or_lt_of_le h2 with e | l2
      · exact Or.inr e
      · exact (hmin U ⟨hU, l⟩ l2).elim

theorem UpperTheory.Gal.Int.Geo.flagEx_of :
    FlagEx := by
  intro Γ k _ _ d ρ
  choose f hf using
    (fun (W : {W : Submodule k (Fin d → k) // IsInv ρ W}) => flag_step ρ W.1 W.2)
  let S : ℕ → {W : Submodule k (Fin d → k) // IsInv ρ W} :=
    fun i => Nat.rec ⟨⊥, inv_bot ρ⟩ (fun _ w => ⟨f w, (hf w).1⟩) i
  have key : ∀ i, (S i).1 = ⊤ ∨ i ≤ Module.finrank k (S i).1 := by
    intro i
    induction i with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      by_cases ht : (S n).1 = ⊤
      · left
        have h1 : (S n).1 ≤ (S (n + 1)).1 := (hf (S n)).2.1
        rw [ht] at h1
        exact top_le_iff.1 h1
      · right
        have hlt : (S n).1 < (S (n + 1)).1 := (hf (S n)).2.2.1 ht
        have h2 := Submodule.finrank_lt_finrank_of_lt hlt
        rcases ih with h | h
        · exact absurd h ht
        · omega
  refine ⟨fun i => (S i).1, monotone_nat_of_le_succ fun i => (hf (S i)).2.1, rfl, ?_,
    fun i => (S i).2, fun i U hU h1 h2 => (hf (S i)).2.2.2 U hU h1 h2⟩
  rcases key d with h | h
  · exact h
  · apply Submodule.eq_top_of_finrank_eq
    have h3 := Submodule.finrank_le (S d).1
    simp only [Module.finrank_fin_fun] at h3 ⊢
    omega
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.grHom_of :
    GrHom := by
  intro Γ k _ _ d ρ₀ c hinv
  have mem : ∀ (i : ℕ) (v : Fin d → k), v ∈ low k c i ↔ ∀ j, i ≤ c j → v j = 0 :=
    fun _ _ => Iff.rfl
  have hbt : ∀ g, (ρ₀ g : Matrix (Fin d) (Fin d) k).BlockTriangular c := by
    intro g i j hij
    have hv : (Pi.single j (1 : k) : Fin d → k) ∈ low k c (c j + 1) := by
      rw [mem]
      intro j' hj'
      by_cases h : j' = j
      · subst h
        omega
      · simp [Pi.single_apply, h]
    have hw := (mem _ _).1 (hinv (c j + 1) g _ hv) i (by omega)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hw
  let D : Matrix (Fin d) (Fin d) k → Matrix (Fin d) (Fin d) k :=
    fun M => Matrix.of fun i j => if c i = c j then M i j else 0
  have hD : ∀ M i j, D M i j = if c i = c j then M i j else 0 := fun _ _ _ => rfl
  have hmul : ∀ M N : Matrix (Fin d) (Fin d) k, M.BlockTriangular c → N.BlockTriangular c →
      D (M * N) = D M * D N := by
    intro M N hM hN
    ext i j
    simp only [hD, Matrix.mul_apply]
    split_ifs with hij
    · apply Finset.sum_congr rfl
      intro l _
      by_cases h1 : c i = c l
      · rw [if_pos h1, if_pos (h1 ▸ hij)]
      · rw [if_neg h1, zero_mul]
        rcases lt_or_gt_of_ne h1 with h | h
        · rw [hN (show c j < c l by omega), mul_zero]
        · rw [hM h, zero_mul]
    · symm
      apply Finset.sum_eq_zero
      intro l _
      split_ifs with h1 h2 <;> simp_all
  have hone : D 1 = 1 := by
    ext i j
    simp only [hD, Matrix.one_apply]
    split_ifs <;> simp_all
  have hunit : ∀ g h : Γ, D (ρ₀ g) * D (ρ₀ h) = D (ρ₀ (g * h)) := by
    intro g h
    rw [← hmul _ _ (hbt g) (hbt h), map_mul, Units.val_mul]
  refine ⟨hbt, ⟨{ toFun := fun g => ⟨D (ρ₀ g), D (ρ₀ g⁻¹), ?_, ?_⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩⟩
  · rw [hunit, mul_inv_cancel, map_one, Units.val_one, hone]
  · rw [hunit, inv_mul_cancel, map_one, Units.val_one, hone]
  · apply Units.ext
    show D (ρ₀ 1) = 1
    rw [map_one, Units.val_one, hone]
  · intro x y
    apply Units.ext
    show D (ρ₀ (x * y)) = D (ρ₀ x) * D (ρ₀ y)
    rw [hunit]
  · intro g i j
    rfl
end

section

open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem exists_linearIndep_levels_span_eq_of_monotone {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (hW : Monotone W) (h0 : W 0 = ⊥) (n : ℕ) :
    ∃ (s : Set V) (lev : V → ℕ), LinearIndepOn k id s ∧ (∀ x ∈ s, lev x < n) ∧
      ∀ i ≤ n, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
  induction n with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [h0]
  | succ n ih =>
    obtain ⟨s, lev, hs, hlev, hspan⟩ := ih
    have hsW : s ⊆ (W (n + 1) : Set V) := by
      intro x hx
      have hx' : x ∈ W n := by
        rw [← hspan n le_rfl]
        exact Submodule.subset_span ⟨hx, hlev x hx⟩
      exact hW (Nat.le_succ n) hx'
    obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension hs hsW
    classical
    refine ⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ s
      · simp only [h, if_true]
        exact Nat.lt_succ_of_lt (hlev x h)
      · simp [h]
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i} := by
          ext x
          by_cases h : x ∈ s
          · simp [h, hsb h]
          · simp only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]
            rintro ⟨-, h'⟩
            omega
        rw [hset]
        exact hspan i (Nat.lt_succ_iff.mp hi')
      · have hi2 : i = n + 1 := le_antisymm hi hi'
        subst hi2
        have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b := by
          ext x
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            by_cases h : x ∈ s
            · simp only [h, if_true]
              exact Nat.lt_succ_of_lt (hlev x h)
            · simp [h]
        rw [hset]
        apply le_antisymm
        · exact Submodule.span_le.mpr hbt
        · intro y hy
          exact htb hy

theorem UpperTheory.Gal.Int.Geo.flagBasis_of :
    FlagBasis := by
  intro k _ d m W hW h0 hm
  obtain ⟨s, lev, hs, hlev, hspan⟩ := exists_linearIndep_levels_span_eq_of_monotone W hW h0 m
  have hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
    intro i
    rcases le_or_gt i m with h | h
    · exact hspan i h
    · have e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m} := by
        ext x
        constructor
        · rintro ⟨hx, -⟩
          exact ⟨hx, hlev x hx⟩
        · rintro ⟨hx, h'⟩
          exact ⟨hx, by omega⟩
      have hle := hW h.le
      rw [hm] at hle
      rw [e1, hspan m le_rfl, hm]
      exact (top_le_iff.mp hle).symm
  have hsall : Submodule.span k s = ⊤ := by
    have e1 : {x | x ∈ s ∧ lev x < m} = s := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩
    rw [← e1, hspan m le_rfl, hm]
  let b0 : Module.Basis s k (Fin d → k) :=
    Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)
  let e : s ≃ Fin d := b0.indexEquiv (Pi.basisFun k (Fin d))
  let b : Module.Basis (Fin d) k (Fin d → k) := b0.reindex e
  have hb : ∀ j, b j = (e.symm j : Fin d → k) := by
    intro j
    simp only [b, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  let L := b.equivFun.symm
  let P : GL (Fin d) k :=
    ⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)),
      LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)),
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun j => lev (e.symm j), ?_⟩
  intro i v
  have hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v := LinearMap.toMatrix'_mulVec _ v
  rw [hPv, ← hall i]
  have himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb]
      exact ⟨(e.symm j).2, hj⟩
    · rintro ⟨hx, hl⟩
      refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hl
      · rw [hb]
        simp
  rw [← himg, Module.Basis.mem_span_image]
  have hrep : ⇑(b.repr (L v)) = v := by
    rw [← Module.Basis.equivFun_apply]
    exact b.equivFun.apply_symm_apply v
  constructor
  · intro hv j hj
    change ∀ j, i ≤ lev (e.symm j) → v j = 0 at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
    show lev (e.symm j) < i
    by_contra hlt
    exact hj (hv j (not_lt.mp hlt))
  · intro hsub
    change ∀ j, i ≤ lev (e.symm j) → v j = 0
    intro j hj
    by_contra hne
    have hmem : j ∈ ((b.repr (L v)).support : Set (Fin d)) := by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep]
      exact hne
    have h2 := hsub hmem
    simp only [Set.mem_setOf_eq] at h2
    omega
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem finOfDeg {K : Type} [Field K] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)] (hf : ∀ n, FiniteDimensional K (A n)) (N : ℤ)
    (hs : ∀ n, (n < 0 ∨ N < n) → Subsingleton (A n)) :
    FiniteDimensional K (DirectSum ℤ A) := by
  classical
  let S : Finset ℤ := Finset.Icc 0 N
  have hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      by_cases hi : i ∈ S
      · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)
      · have hout : i < 0 ∨ N < i := by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          exact hi
        haveI := hs i hout
        rw [Subsingleton.elim a 0, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤ :=
    eq_top_iff.2 (fun x _ => hall x)
  refine Module.finite_def.2 ?_
  rw [← htop]
  refine Submodule.fg_biSup S _ (fun n _ => ?_)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.1 (hf n)).map _

theorem UpperTheory.Gal.Int.Geo.htotFin_of :
    DegFin → HtotFin := by
  intro h l _ k _ _ hl X p hp hproj
  obtain ⟨hf, N, hN⟩ := h l k hl p hp hproj
  exact finOfDeg hf N hN
end
