module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

namespace PositivityTheory.Xgf.EigenspaceComposition

open GlobalTheory.CompanionTheory.Ar

variable {F F' : Type} [Field F] [Field F'] (f : F →+* F') {N : ℕ} {O : Type} [CommRing O]
  (ρ : O →+* Module.End F (Fin N → F)) (ρ' : O →+* Module.End F' (Fin N → F')) (τ : O →+* F)

theorem mem_eigSp {K : Type} [Field K] {ρ : O →+* Module.End K (Fin N → K)} {σ : O →+* K} (w : Fin N → K) :
    w ∈ eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem comp_smul (c : F) (w : Fin N → F) : f ∘ (c • w) = f c • (f ∘ w) := by
  funext i; simp

theorem comp_inj : Function.Injective fun w : Fin N → F => f ∘ w := fun w w' h =>
  funext fun i => f.injective (congrFun h i)

theorem comp_add (w w' : Fin N → F) : f ∘ (w + w') = f ∘ w + f ∘ w' := by funext i; simp

variable {f ρ ρ' τ}

theorem mem_eigSp_comp (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) (w : Fin N → F) :
    f ∘ w ∈ eigSp ρ' (f.comp τ) ↔ w ∈ eigSp ρ τ := by
  rw [mem_eigSp, mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [hρ, RingHom.comp_apply, ← comp_smul]
  exact (comp_inj f).eq_iff

theorem linIndep_comp {ι ι' : Type} [Finite ι'] (u : ι → ι' → F) :
    LinearIndependent F' (fun k => f ∘ u k) ↔ LinearIndependent F u := by
  letI : Algebra F F' := f.toAlgebra
  exact linearIndependent_algebraMap_comp_iff

theorem comp_mem_span {ι : Type} (g : ι → Fin N → F) (w : Fin N → F) (hw : w ∈ Submodule.span F (Set.range g)) :
    f ∘ w ∈ Submodule.span F' (Set.range fun s => f ∘ g s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Submodule.subset_span ⟨s, rfl⟩
  | zero =>
    have : f ∘ (0 : Fin N → F) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [comp_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [comp_smul]; exact Submodule.smul_mem _ _ hx

theorem span_comp_eq (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (b : Fin n → Fin N → F)
    (hli : LinearIndependent F b) (hsp : Submodule.span F (Set.range b) = eigSp ρ τ) :
    Submodule.span F' (Set.range fun k => f ∘ b k) = eigSp ρ' (f.comp τ) := by
  classical
  have hbW : ∀ k, b k ∈ eigSp ρ τ := fun k => hsp ▸ Submodule.subset_span ⟨k, rfl⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (mem_eigSp_comp hρ (b k)).2 (hbW k)
  intro w' hw'
  have hbρ : ∀ a k, ρ a (b k) = τ a • b k := fun a k => (mem_eigSp (b k)).1 (hbW k) a

  obtain ⟨A0, hA0⟩ : ∃ A0 : Finset O, ∀ w, (∀ a ∈ A0, ρ a w = τ a • w) → w ∈ eigSp ρ τ := by
    let T : Set (Submodule F (Fin N → F)) :=
      {K | ∃ A : Finset O, K = ⨅ a ∈ A, LinearMap.ker (ρ a - τ a • LinearMap.id)}
    obtain ⟨K, ⟨A, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal T ⟨_, ⟨∅, rfl⟩⟩
    refine ⟨A, fun w hw => (mem_eigSp w).2 fun a => ?_⟩
    have hle : (⨅ a' ∈ insert a A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)) ≤
        ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) :=
      iInf_mono fun a' => iInf_mono' fun h => ⟨Finset.mem_insert_of_mem h, le_rfl⟩
    have heq := (eq_of_le_of_not_lt hle (hmin _ ⟨insert a A, rfl⟩))
    have hwK : w ∈ ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact hw
    rw [← heq] at hwK
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hwK
    exact hwK a (Finset.mem_insert_self a A)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (eigSp ρ τ)
  let bc := Module.finBasis F C
  let c : Fin (Module.finrank F C) → Fin N → F := fun j => (bc j : Fin N → F)
  let g : Fin n ⊕ Fin (Module.finrank F C) → Fin N → F := Sum.elim b c
  have gspan : Submodule.span F (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hsp]
      exact Submodule.span_mono fun _ ⟨k, hk⟩ => ⟨Sum.inl k, hk⟩
    · intro v hv
      have hr := bc.sum_repr ⟨v, hv⟩
      have hv2 : v = ((∑ j, bc.repr ⟨v, hv⟩ j • bc j : C) : Fin N → F) := by rw [hr]
      rw [hv2, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have g'span : Submodule.span F' (Set.range fun s => f ∘ g s) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : F') else 0) = f ∘ (fun j => if i = j then (1 : F) else 0) := by
      funext j; by_cases h : i = j <;> simp [h]
    rw [e]
    exact comp_mem_span g _ (gspan ▸ Submodule.mem_top)
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun F').1 (g'span ▸ (Submodule.mem_top : w' ∈ ⊤))
  rw [Fintype.sum_sum_type] at hz
  simp only [g, Sum.elim_inl, Sum.elim_inr] at hz
  let V : Fin (Module.finrank F C) → A0 × Fin N → F := fun j p => (ρ p.1 (c j) - τ p.1 • c j) p.2
  have hV : LinearIndependent F V := by
    rw [Fintype.linearIndependent_iff]
    intro y hy j
    have hmem : ∑ j, y j • c j ∈ eigSp ρ τ := by
      refine hA0 _ fun a ha => ?_
      rw [← sub_eq_zero]
      funext i
      have := congrFun hy (⟨a, ha⟩, i)
      simp only [V, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this

      simp only [map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hCm : ∑ j, y j • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (bc j).2
    have h0 : ∑ j, y j • c j = 0 := (Submodule.disjoint_def.1 hC.disjoint) _ hmem hCm
    have h1 : ∑ j, y j • bc j = 0 := Subtype.ext (by simpa [c] using h0)
    exact Fintype.linearIndependent_iff.1 bc.linearIndependent y h1 j
  have hV' := (linIndep_comp (f := f) V).2 hV
  have hL : ∀ a, ∑ j, z (Sum.inr j) • (f ∘ (ρ a (c j) - τ a • c j)) = 0 := by
    intro a
    have e1 : ρ' a w' - f (τ a) • w' = 0 := sub_eq_zero.2 ((mem_eigSp w').1 hw' a)
    rw [← hz] at e1

    simp only [map_add (f := _), map_sum, map_smul, hρ, hbρ, comp_smul] at e1
    have hs : ∀ x y : Fin N → F, f ∘ (x - y) = f ∘ x - f ∘ y := fun x y => by funext i; simp
    simp only [hs, comp_smul]
    rw [← e1]
    simp only [smul_add, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    have hc1 : ∀ x, f (τ a) • z (Sum.inl x) • (f ∘ b x) = z (Sum.inl x) • f (τ a) • (f ∘ b x) :=
      fun x => smul_comm _ _ _
    have hc2 : ∀ x, f (τ a) • z (Sum.inr x) • (f ∘ c x) = z (Sum.inr x) • f (τ a) • (f ∘ c x) :=
      fun x => smul_comm _ _ _
    simp only [hc1, hc2]
    abel
  have hy : ∀ j, z (Sum.inr j) = 0 := by
    have hsum : ∑ j, z (Sum.inr j) • (f ∘ V j) = 0 := by
      funext p
      have := congrFun (hL p.1.1) p.2
      simpa [V, Finset.sum_apply] using this
    intro j
    exact Fintype.linearIndependent_iff.1 hV' _ hsum j
  rw [← hz]
  simp only [hy, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem core (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (u : Fin n → Fin N → F) :
    (LinearIndependent F u ∧ Submodule.span F (Set.range u) = eigSp ρ τ) ↔
      (LinearIndependent F' (fun k => f ∘ u k) ∧ Submodule.span F' (Set.range fun k => f ∘ u k) = eigSp ρ' (f.comp τ)) := by
  constructor
  · rintro ⟨hli, hsp⟩
    exact ⟨(linIndep_comp (ι' := Fin N) u).2 hli, span_comp_eq hρ u hli hsp⟩
  · rintro ⟨hli', hsp'⟩
    have hli := (linIndep_comp (ι' := Fin N) u).1 hli'
    refine ⟨hli, ?_⟩
    have hmem : ∀ k, u k ∈ eigSp ρ τ := fun k =>
      (mem_eigSp_comp hρ (u k)).1 (hsp' ▸ Submodule.subset_span ⟨k, rfl⟩)
    have hle : Submodule.span F (Set.range u) ≤ eigSp ρ τ := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hmem k

    let W := eigSp ρ τ
    let bW := Module.finBasis F W
    let b : Fin (Module.finrank F W) → Fin N → F := fun j => (bW j : Fin N → F)
    have hbli : LinearIndependent F b := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hbsp : Submodule.span F (Set.range b) = W := by
      have : Set.range b = W.subtype '' Set.range bW := by rw [← Set.range_comp]; rfl
      rw [this, Submodule.span_image, bW.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hW' := span_comp_eq hρ b hbli hbsp
    have e1 : Module.finrank F' (eigSp ρ' (f.comp τ)) = n := by
      rw [← hsp', finrank_span_eq_card hli', Fintype.card_fin]
    have e2 : Module.finrank F' (eigSp ρ' (f.comp τ)) = Module.finrank F W := by
      rw [← hW', finrank_span_eq_card ((linIndep_comp (ι' := Fin N) b).2 hbli), Fintype.card_fin]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin, ← e1, e2]

end PositivityTheory.Xgf.EigenspaceComposition
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section Ultra

variable {A : Type} [NormedField A] [IsUltrametricDist A]

theorem norm_sign_smul {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (x : A) :
    ‖Equiv.Perm.sign σ • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, Units.smul_def]

theorem ultrametric_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → A) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
  exact hle.trans_lt (h i hi)

theorem ultrametric_norm_prod_sub_lt {ι : Type} (s : Finset ι) (a b : ι → A) {r : ℝ} (hr : 0 < r) (ha : ∀ i ∈ s, ‖a i‖ ≤ r)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ r) (hab : ∀ i ∈ s, ‖a i - b i‖ < r) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have hpb : ‖∏ i ∈ s, b i‖ ≤ r ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, r :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i hi => hb i (Finset.mem_insert_of_mem hi)
        _ = r ^ s.card := Finset.prod_const r
    have hpos : 0 < r ^ (s.card + 1) := pow_pos hr _
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, pow_succ']
      rcases (norm_nonneg (a j)).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; exact pow_pos hr _ |>.trans_le (by rw [pow_succ'])
      · calc ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < ‖a j‖ * r ^ s.card := mul_lt_mul_of_pos_left ih' h0
          _ ≤ r * r ^ s.card := mul_le_mul_of_nonneg_right (ha j (Finset.mem_insert_self _ _)) (pow_nonneg hr.le _)
    · rw [norm_mul, pow_succ']
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hab j (Finset.mem_insert_self _ _)) hpb (norm_nonneg _)
        (pow_pos hr _)

end Ultra

theorem ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  intro A _ _ I _ _ M M' r hr hM hM' hdet
  have hM'b : ∀ a b, ‖M' a b‖ ≤ r := fun a b => by
    have := IsUltrametricDist.norm_add_le_max (M' a b - M a b) (M a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM' a b).le (hM a b))
  have hdiff : ‖M'.det - M.det‖ < r ^ Fintype.card I := by
    rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
    refine ultrametric_norm_sum_lt _ _ (pow_pos hr _) fun σ _ => ?_
    rw [← smul_sub, norm_sign_smul, ← Finset.card_univ]
    exact ultrametric_norm_prod_sub_lt _ _ _ hr (fun i _ => hM'b _ _) (fun i _ => hM _ _) fun i _ => hM' _ _
  have e : M'.det = M.det + (M'.det - M.det) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdet]; exact hdiff.ne'), hdet]
  exact max_eq_left hdiff.le

theorem negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  intro p q A B C hA hB hC
  let C1 : Matrix (Fin q) (Fin p) ℂ := fun a i => C a (Sum.inl i)
  let C2 : Matrix (Fin q) (Fin q) ℂ := fun a i => C a (Sum.inr i)
  have hsplit : C * Matrix.fromBlocks A 0 0 B * Cᴴ = C1 * A * C1ᴴ + C2 * B * C2ᴴ := by
    have hCe : C = Matrix.fromCols C1 C2 := by ext a (i | i) <;> rfl
    rw [hCe, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hP : (C2 * (-B) * C2ᴴ).PosDef := by
    have e : C2 * (-B) * C2ᴴ = -(C * Matrix.fromBlocks A 0 0 B * Cᴴ) + C1 * A * C1ᴴ := by
      rw [hsplit]; noncomm_ring
    rw [e]
    exact hC.add_posSemidef (hA.posSemidef.mul_mul_conjTranspose_same C1)
  have hinj : Function.Injective (C2ᴴ).mulVec := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (C2ᴴ) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := hP.dotProduct_mulVec_pos hz
    rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hU : IsUnit (C2ᴴ) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hG : C2ᴴ * (C2ᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hGinj : Function.Injective ((C2ᴴ)⁻¹).mulVec := fun x y hxy => by
    have := congrArg (C2ᴴ).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have key := hP.conjTranspose_mul_mul_same (B := (C2ᴴ)⁻¹) hGinj
  have h1 : ((C2ᴴ)⁻¹)ᴴ * C2 = 1 := by
    have := congrArg Matrix.conjTranspose hG
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  have e : ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = -B := by
    calc ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = (((C2ᴴ)⁻¹)ᴴ * C2) * -B * (C2ᴴ * (C2ᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = -B := by rw [h1, hG, Matrix.one_mul, Matrix.mul_one]
  rwa [e] at key

end PositivityTheory.Xgf
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

namespace NP

open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 k)) : ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
  have hP : ∀ n : ℕ, n ≠ 0 → (n : 𝓞 k) ∈ v.asIdeal → ∃ p : Nat.Primes, ((p : ℕ) : 𝓞 k) ∈ v.asIdeal := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd (by simpa using h) (v.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2)
    | prime q hq => intro _ h; exact ⟨⟨q, hq⟩, h⟩
    | mul a b ha hb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact ha (fun h0 => hab (by rw [h0, zero_mul])) h
      · exact hb (fun h0 => hab (by rw [h0, mul_zero])) h
  exact hP _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem v.asIdeal)

theorem prime_unique (v : HeightOneSpectrum (𝓞 k)) {p q : Nat.Primes} (hp : ((p : ℕ) : 𝓞 k) ∈ v.asIdeal)
    (hq : ((q : ℕ) : 𝓞 k) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes p.2 q.2).2 fun h => hne (Subtype.ext h)
  obtain ⟨u, w, huw⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 k))
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huw]
  simp only [eq_intCast, Int.cast_natCast]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hq)

theorem finite_over (p : Nat.Primes) : {v : HeightOneSpectrum (𝓞 k) | ((p : ℕ) : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((p : ℕ) : 𝓞 k)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end NP

end PositivityTheory.Xgf
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

theorem exists_integer_near_conj_vector : ∀ (E : Type) [Field E] [NumberField E], ∃ B : ℝ, ∀ c : (E →+* ℂ) → ℂ, (∀ τ, c (ComplexEmbedding.conjugate τ) = starRingEnd ℂ (c τ)) → ∃ a : 𝓞 E, ∀ τ : E →+* ℂ, ‖τ (a : E) - c τ‖ ≤ B := by
  intro E _ _
  classical
  obtain ⟨bC, hv⟩ : ∃ bC : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ ((E →+* ℂ) → ℂ),
      ∀ i (τ : E →+* ℂ), bC i τ = τ (RingOfIntegers.basis E i : E) :=
    ⟨canonicalEmbedding.latticeBasis E, fun i τ => by
      rw [canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, integralBasis_apply]⟩
  refine ⟨∑ τ : E →+* ℂ, ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖, fun c hc => ?_⟩
  have hsum : c = ∑ i, bC.repr c i • bC i := (bC.sum_repr c).symm
  have hcτ : ∀ τ : E →+* ℂ, c τ = ∑ i, bC.repr c i * τ (RingOfIntegers.basis E i : E) := by
    intro τ
    conv_lhs => rw [hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
  have hconj : ∀ τ : E →+* ℂ,
      ∑ i, starRingEnd ℂ (bC.repr c i) * τ (RingOfIntegers.basis E i : E) = c τ := by
    intro τ
    have h1 := hc τ
    rw [hcτ (ComplexEmbedding.conjugate τ)] at h1
    have h2 := congrArg (starRingEnd ℂ) h1

    rw [Complex.conj_conj, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hli := Fintype.linearIndependent_iff.mp bC.linearIndependent
    (fun i => bC.repr c i - starRingEnd ℂ (bC.repr c i)) (by
      funext τ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hv, sub_mul,
        Finset.sum_sub_distrib]
      rw [hconj τ, ← hcτ τ, sub_self])
  have hreal : ∀ i, (bC.repr c i).im = 0 := by
    intro i
    have h3 := congrArg Complex.im (hli i)
    rw [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im] at h3
    linarith
  obtain ⟨x, hx⟩ : ∃ x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ i, bC.repr c i = (x i : ℂ) :=
    ⟨fun i => (bC.repr c i).re, fun i => Complex.ext (by simp) (by simp [hreal i])⟩
  refine ⟨∑ i, round (x i) • RingOfIntegers.basis E i, fun τ => ?_⟩
  have hτa : τ ((∑ i, round (x i) • RingOfIntegers.basis E i : 𝓞 E) : E) =
      ∑ i, (round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    change (τ.comp (algebraMap (𝓞 E) E)) (∑ i, round (x i) • RingOfIntegers.basis E i) = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have hcx : c τ = ∑ i, (x i : ℂ) * τ (RingOfIntegers.basis E i : E) := by
    rw [hcτ τ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
  rw [hτa, hcx, ← Finset.sum_sub_distrib]
  calc ‖∑ i, ((round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E))‖
      ≤ ∑ i, ‖(round (x i) : ℂ) * τ (RingOfIntegers.basis E i : E) -
          (x i : ℂ) * τ (RingOfIntegers.basis E i : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖τ (RingOfIntegers.basis E i : E)‖ := Finset.sum_le_sum fun i _ => by
        rw [← sub_mul, norm_mul]
        have hr : ‖(round (x i) : ℂ) - (x i : ℂ)‖ ≤ 1 := by
          have h := abs_sub_round (x i)
          rw [show ((round (x i) : ℤ) : ℂ) - ((x i : ℝ) : ℂ) = (((round (x i) : ℝ) - x i : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
          linarith
        calc ‖(round (x i) : ℂ) - (x i : ℂ)‖ * ‖τ (RingOfIntegers.basis E i : E)‖
            ≤ 1 * ‖τ (RingOfIntegers.basis E i : E)‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
          _ = ‖τ (RingOfIntegers.basis E i : E)‖ := one_mul _
    _ ≤ ∑ τ' : E →+* ℂ, ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖ :=
        Finset.single_le_sum (f := fun τ' : E →+* ℂ => ∑ i, ‖τ' (RingOfIntegers.basis E i : E)‖)
          (fun τ' _ => Finset.sum_nonneg fun i _ => norm_nonneg _) (Finset.mem_univ τ)

end PositivityTheory.Xgf

end
end
