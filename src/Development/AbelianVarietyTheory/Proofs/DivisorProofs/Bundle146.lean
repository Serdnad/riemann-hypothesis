module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

section

open Filter Topology

namespace GlobalTheory.InvolutionNorm

theorem exists_compact_mod_kernel : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  intro Z _ _ _ _ _ _ hc τ hτ hinv hW D hD
  obtain ⟨W, hW1, hWs⟩ := hW
  let N : Z →* Z :=
    { toFun := fun z => τ z * z
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (τ b) a b, hc (τ b) a, mul_assoc] }
  have hN : Continuous N := hτ.mul continuous_id
  have hNval : ∀ z, N z = τ z * z := fun _ => rfl
  let I : Subgroup Z := N.range
  have hIH : ∀ y ∈ I, τ y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hNval, map_mul, hinv, hc]
  have hHcl : IsClosed {y : Z | τ y = y} := isClosed_eq hτ continuous_id
  have hIcl : IsClosed (I : Set Z) := by
    refine closure_subset_iff_isClosed.1 fun x hx => ?_
    have hxH : τ x = x := closure_minimal (fun y hy => hIH y hy) hHcl hx
    have hnb : (fun y => x⁻¹ * y) ⁻¹' W ∈ 𝓝 x := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW1
    obtain ⟨i, hiW, hiI⟩ := mem_closure_iff_nhds.1 hx _ hnb
    have hiH : τ i = i := hIH i hiI
    obtain ⟨r, hr, hrr⟩ := hWs _ hiW (by rw [map_mul, map_inv, hxH, hiH])
    have hNr : N r = x⁻¹ * i := by rw [hNval, hr, hrr]
    have : x = i * (N r)⁻¹ := by rw [hNr]; group
    rw [this]
    exact I.mul_mem hiI (I.inv_mem ⟨r, rfl⟩)
  let f : Z →* I := N.rangeRestrict
  have hfc : Continuous f := hN.subtype_mk _
  have hfs : Function.Surjective f := N.rangeRestrict_surjective
  have : LocallyCompactSpace I := hIcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hopen : IsOpenMap f := f.isOpenMap_of_sigmaCompact hfs hfc
  have hK' : IsCompact (Subtype.val ⁻¹' D : Set I) :=
    hIcl.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have key : ∃ C : Set Z, IsCompact C ∧ (Subtype.val ⁻¹' D : Set I) ⊆ f '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set Z, IsCompact C ∧ s ⊆ f '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · intro y _
      obtain ⟨g, rfl⟩ := hfs y
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, hCD⟩ := key
  refine ⟨C, hC, fun z hz => ?_⟩
  obtain ⟨c, hcC, e⟩ := hCD (a := f z) hz
  have e' : N c = N z := congrArg Subtype.val e
  refine ⟨z * c⁻¹, ?_, c, hcC, by group⟩
  rw [← hNval, map_mul, map_inv, e', mul_inv_cancel]

end GlobalTheory.InvolutionNorm
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.VolBoxMajorant

theorem tsum_pi_prod_ennreal' : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.VolBoxMajorant

namespace GlobalTheory.VolBoxMajorant

end GlobalTheory.VolBoxMajorant
end

section

open TopologicalSpace Order

namespace GlobalTheory.DimDrop

theorem length_le_topologicalKrullDim_of_last_subset {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hsub : ∀ i, (q i : Set X) ⊆ Z := fun i x hx => h (q.monotone (Fin.le_last i) hx)
  have irr : ∀ i, IsIrreducible (Subtype.val ⁻¹' (q i : Set X) : Set Z) := by
    intro i
    haveI : IrreducibleSpace (q i : Set X) := Subtype.irreducibleSpace (q i).isIrreducible
    have := (IrreducibleSpace.isIrreducible_univ (q i : Set X)).image (Set.inclusion (hsub i))
      (continuous_inclusion (hsub i)).continuousOn
    rw [Set.image_univ, Set.range_inclusion] at this
    exact this
  let f : Fin (q.length + 1) → IrreducibleCloseds Z := fun i =>
    ⟨Subtype.val ⁻¹' (q i : Set X), irr i, (q i).isClosed.preimage continuous_subtype_val⟩
  have hf : ∀ i j, f i = f j → q i = q j := by
    intro i j e
    have e' : (Subtype.val ⁻¹' (q i : Set X) : Set Z) = Subtype.val ⁻¹' (q j : Set X) :=
      congrArg SetLike.coe e
    have e'' := congrArg (Set.image (Subtype.val : Z → X)) e'
    rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (hsub i), Set.inter_eq_right.2 (hsub j)] at e''
    exact SetLike.coe_injective e''
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := q.length
      toFun := f
      step := fun i => by
        have hs : q i.castSucc < q i.succ := q.step i
        show f i.castSucc < f i.succ
        refine lt_of_le_of_ne ?_ fun e => hs.ne (hf _ _ e)
        intro x hx
        exact hs.le hx }
  exact LTSeries.length_le_krullDim p

theorem topologicalKrullDim_lt_of_isClosed (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨p, hp⟩ := le_krullDim_iff.1 hlt
  let q : LTSeries (IrreducibleCloseds S) :=
    p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
      (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hql : q.length = d := hp
  have hWC : (q.last : Set S) ⊆ C := by
    show closure (Subtype.val '' (p.last : Set C)) ⊆ C
    refine closure_minimal ?_ hC
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Z, hZc, hWZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ q.last.isIrreducible
  by_cases hEq : (q.last : Set S) = Z
  · refine hZ Z hZc ?_ (hEq ▸ hWC)
    have := length_le_topologicalKrullDim_of_last_subset Z q hEq.le
    rwa [hql] at this
  · let Zt : IrreducibleCloseds S := ⟨Z, hZc.1, isClosed_of_mem_irreducibleComponents Z hZc⟩
    have hlt' : q.last < Zt := lt_of_le_of_ne hWZ fun e => hEq (congrArg SetLike.coe e)
    have h1 := LTSeries.length_le_krullDim (q.snoc Zt hlt')
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      have e : (q.snoc Zt hlt').length = d + 1 := by simp [hql]
      rw [e] at h1
      exact h1.trans hS
    norm_cast at h2
    omega

theorem finite_of_topologicalKrullDim_nonpos (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 h
  have hcomp : ∀ x : S, closure ({x} : Set S) ∈ irreducibleComponents S := by
    intro x
    refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
    have := hm ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (b := ⟨closure T, hT.closure, isClosed_closure⟩) (fun y hy => subset_closure (hle hy))
    exact subset_closure.trans this
  haveI : Finite (irreducibleComponents S) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective (fun x => (⟨closure {x}, hcomp x⟩ : irreducibleComponents S))
    fun x y hxy => (inseparable_iff_closure_eq.2 (congrArg Subtype.val hxy)).eq

theorem dim_drop : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S],
    (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d →
      (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) →
      topologicalKrullDim C < d) ∧
    (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  intro S _ _
  exact ⟨fun C d hC hS hZ => topologicalKrullDim_lt_of_isClosed S C d hC hS hZ,
    fun _ h => finite_of_topologicalKrullDim_nonpos S h⟩

end GlobalTheory.DimDrop
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DimCodim

section

attribute [local instance low] specializationOrder

theorem dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by
  have hmono : StrictMono j := by
    intro x y hxy
    refine lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))
    exact (show y ⤳ x from hxy.le).map hj
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [Order.krullDim_eq_bot]
    simp
  · have : Nonempty S := ⟨j hW.some⟩
    rw [Order.krullDim_eq_iSup_height_of_nonempty,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    refine iSup_le fun w => le_trans ?_
      (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))
    exact add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)

end

end GlobalTheory.DimCodim
end

section

open Filter Topology

namespace GlobalTheory

theorem tendsto_div_add_const_pow_div_pow (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp

theorem tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  choose! c c' hc using h
  set C := ∑ s ∈ Finset.range e, c s with hC
  set C' := ∑ s ∈ Finset.range e, c' s with hC'
  have hcC : ∀ s, s < e → c s ≤ C := fun s hs =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have hcC' : ∀ s, s < e → c' s ≤ C' := fun s hs =>
    Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial *
      (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
    intro K
    have := (tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)
    convert this using 2
    rw [div_pow, one_pow]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have hqC : C ≤ m / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
    have hcs := hcC (m % e) hs
    have h1 := (hc (m % e) hs (m / e - c (m % e))).1
    rw [Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq] at h1
    have h2 := Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)
    have h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1 := by omega
    rw [h3] at h2
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hsR : ((m % e : ℕ) : ℝ) < e := by exact_mod_cast hs
    have hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ heR]; nlinarith
    have hge : (C : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]
      have : ((e * C : ℕ) : ℝ) ≤ m := by exact_mod_cast (show e * C ≤ m by omega)
      push_cast at this; linarith
    have hcsR : (c (m % e) : ℝ) ≤ C := by exact_mod_cast hcs
    have hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ) := by linarith
    have hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m := by
      calc (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D
          ≤ (δ : ℝ) / D.factorial * (((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D := by gcongr
        _ = (δ : ℝ) * ((((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D / D.factorial) := by ring
        _ ≤ (δ : ℝ) * ((m / e - c (m % e) + D).choose D : ℝ) := by gcongr
        _ ≤ r m := by exact_mod_cast h1
    calc (δ : ℝ) / D.factorial * (((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D)
        = (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D := by ring
      _ ≤ (r m : ℝ) / (m : ℝ) ^ D := by gcongr
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have h1 := (hc (m % e) hs (m / e)).2
    rw [hm_eq] at h1
    have h2 := Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]; nlinarith
    have hcsR : (c' (m % e) : ℝ) ≤ C' := by exact_mod_cast hcC' (m % e) hs
    have hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D := by
      calc (r m : ℝ) ≤ (δ : ℝ) * ((m / e + c' (m % e) + D).choose D : ℝ) := by exact_mod_cast h1
        _ ≤ (δ : ℝ) * (((m / e + c' (m % e) + D : ℕ) : ℝ) ^ D / D.factorial) := by gcongr
        _ = (δ : ℝ) / D.factorial * (((m / e + c' (m % e) + D : ℕ) : ℝ)) ^ D := by ring
        _ ≤ _ := by gcongr
    calc (r m : ℝ) / (m : ℝ) ^ D
        ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D / (m : ℝ) ^ D := by gcongr
      _ = _ := by ring

end GlobalTheory
end
