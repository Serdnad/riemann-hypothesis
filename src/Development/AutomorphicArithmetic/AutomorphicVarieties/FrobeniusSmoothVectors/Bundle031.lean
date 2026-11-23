module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgebraMapRangeSpanEqTopOfFiniteGenerators
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle026
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_lt {n : ℕ} {i j : Fin n} (h : j < i) : w n i - w n j < 0 := by
  have h' : (j : ℕ) < (i : ℕ) := h
  unfold w
  split_ifs <;> omega

private theorem sum_neg {α : Type} (f : α → ℤ) (L : List α) (h : ∀ s ∈ L, f s ≤ 0) (h' : ∃ s ∈ L, f s < 0) :
    (L.map f).sum < 0 := by
  have key : ∀ L : List α, (∀ s ∈ L, f s ≤ 0) → (L.map f).sum ≤ 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun s hs => h s (by simp [hs]))
      omega
  induction L with
  | nil => simp at h'
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hL : ∀ s ∈ L, f s ≤ 0 := fun s hs => h s (by simp [hs])
    have hsum := key L hL
    obtain ⟨s, hs, hs'⟩ := h'
    rcases List.mem_cons.1 hs with rfl | hs
    · omega
    · have := ih hL ⟨s, hs, hs'⟩
      omega

private theorem lc_hom {k G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group k] (χ : G →* k)
    (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' (χ.ker : Set G), ?_, isOpenMap_mul_left g _ h, ⟨1, χ.ker.one_mem, mul_one g⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : χ x = 1 := MonoidHom.mem_ker.1 hx
  show χ (g * x) = y
  rw [map_mul, hx1, mul_one]
  exact hg


theorem UpperTheory.smoothHom_weight_sum_neg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] (ρ : NRep F n Q), ρ.IsBar (algebraMap (ResidueField O) Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∃ ξ : S.A →+* Q, S.FPt ξ ∧ S.u.map ξ = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ ρ hbar htri hlc
  letI : IsCO O (ResidueField O) := (co_res O).1
  letI : Algebra O Q := ((algebraMap (ResidueField O) Q).comp (algebraMap O (ResidueField O))).toAlgebra
  haveI : IsScalarTower O (ResidueField O) Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CompactSpace F.G0 := by
    have hc : IsCompact (F.del.ker : Set F.Γ) := (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
    exact isCompact_iff_compactSpace.1 hc
  have hres : ∀ c : ResidueField O, res O (ResidueField O) c = c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact (res O (ResidueField O)).commutes a
  have hinj : Function.Injective (algebraMap (ResidueField O) Q) := (algebraMap (ResidueField O) Q).injective
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := by
    intro g i j h
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rw [htri] at hm
    exact Ideal.mem_bot.1 hm
  have hΨ : IsLocallyConstant (F.Ψ : F.Γ → (ResidueField O)ˣ) := lc_hom F.Ψ hF.Ψ_open
  have hcone : Cone O (ResidueField O) ρ := by
    refine ⟨fun g i => ⟨_, (hbar.1 g i).symm, hres _⟩, fun L hsum hex => ?_,
      fun i j => Submodule.fg_span (hlc i j).range_finite, fun i j N => (hlc i j).comp _, ?_⟩
    · refine ⟨0, Ideal.zero_mem _, ?_⟩
      rw [map_zero, eq_comm]
      apply List.prod_eq_zero
      rw [List.mem_map]
      by_contra hcon
      push_neg at hcon
      have hle : ∀ t ∈ L, w n t.2.1 - w n t.2.2 ≤ 0 := by
        intro t ht
        rcases lt_trichotomy t.2.1 t.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon t ht)
        · rw [h, sub_self]
        · exact (w_lt h).le
      obtain ⟨s, hs, hne⟩ := hex
      have hlt : w n s.2.1 - w n s.2.2 < 0 := by
        rcases lt_trichotomy s.2.1 s.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon s hs)
        · exact absurd h hne
        · exact w_lt h
      have h2 : (L.map fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2).sum < 0 :=
        sum_neg (fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2) L hle ⟨s, hs, hlt⟩
      exact absurd hsum (ne_of_lt h2)
    · refine ⟨fun v i g => ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O),
        fun v i => ⟨fun N => ?_, fun g => hres _⟩, fun v i g => (hbar.2 v i g).symm⟩
      have hcont : Continuous (F.loc v) :=
        continuous_subtype_val.comp (hF.loc_cont v)
      exact (hΨ.comp_continuous hcont).comp
        (fun u => Ideal.Quotient.mk (maximalIdeal (ResidueField O) ^ N)
          ((u ^ w n i : (ResidueField O)ˣ) : ResidueField O))
  obtain ⟨ξ, β, hmap, hβ⟩ := alg hF hn S (ResidueField O) Q hinj ρ hcone
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  refine ⟨(ξ : S.A →+* Q), ⟨?_, fun c => ξ.commutes c⟩, hmap⟩
  rw [Space.x0, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hb' : b ∈ maximalIdeal S.B := by rw [hmax]; exact hb
  have h0 : β b = 0 := by
    rw [← hres (β b), res_map β b]
    exact (res_eq_zero_iff O S.B b).2 hb'
  show ξ (S.inc b) = 0
  rw [hβ b, h0, map_zero]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_gen (k Q : Type) [Field k] [CommRing Q] [Algebra k Q] (T : Finset Q) (m : ℕ) (h : T.card ≤ m)
    (ht : Algebra.adjoin k (T : Set Q) = ⊤) : ringKrullDim Q ≤ (m : ℕ) := by
  have hs : Function.Surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa using ht
  refine (ringKrullDim_le_of_surjective (MvPolynomial.aeval (R := k) (fun t : T => (t : Q))).toRingHom hs).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
  exact_mod_cast h

private theorem point {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}
    (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F n Q)
    (hb : ρ.IsBar (algebraMap k Q)) (ht : ρ.triM = ⊥) (hc : ∀ i j, IsLocallyConstant fun g => ρ.r g i j) :
    ∃ T : Finset Q, T.card ≤ 2 * C₀ ∧ ∀ g i j, ρ.r g i j ∈ Algebra.adjoin k (T : Set Q) := by
  classical
  have up : ∀ g i j, i < j → ρ.r g i j = 0 := fun g i j h => by
    have : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rwa [ht, Ideal.mem_bot] at this
  have red : ∀ U : Subalgebra k Q, (∀ g i j, j < i → ρ.r g i j ∈ U) → ∀ g i j, ρ.r g i j ∈ U := fun U h g i j => by
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [up g i j h1]; exact zero_mem _
    · rw [hb.1]; exact U.algebraMap_mem _
    · exact h g i j h1
  rcases hn with rfl | rfl
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_fiber_nonempty hF Q ρ hb ht hc)
    refine ⟨T, by omega, red _ fun g i j h => ?_⟩
    obtain ⟨rfl, rfl⟩ : i = 1 ∧ j = 0 := by omega
    exact Algebra.span_le_adjoin k _ (h2 g)
  · obtain ⟨T, h1, h2⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strY k) C₀ _ (finrank_structMapY_range hF)
      fun f => Frame.strY_map f (framePoint_y_coord_eq hF Q ρ hb ht hc)
    have hy : ∀ g, ρ.r g 1 0 ∈ Algebra.adjoin k (T : Set Q) := fun g => Algebra.span_le_adjoin k _ (h2 g)
    obtain ⟨T', h3, h4⟩ := algebraMap_range_span_eq_top_of_finite_generators (F.strS k) C₀ _ (finrank_structMapS_range hF)
      fun f => Frame.strS_map f (framePoint_alg_coord_eq hF Q ρ hb ht hc _ hy)
    obtain ⟨σ, hσ⟩ := (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ_surjective.hasRightInverse
    have hle : Algebra.adjoin k (T : Set Q) ≤ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) :=
      Algebra.adjoin_mono (by simp)
    refine ⟨T ∪ T'.image σ, (Finset.card_union_le _ _).trans ?_, red _ fun g i j h => ?_⟩
    · have := Finset.card_image_le (s := T') (f := σ)
      omega
    have hij : (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hle (hy g)
    · have h5 : ρ.r (F.star g) 1 0 = ρ.r g 2 1 := (UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0
      rw [← h5]
      exact hle (hy _)
    · have h5 : Submodule.span k (T' : Set _) ≤ (Subalgebra.toSubmodule (Algebra.adjoin k
          ((T ∪ T'.image σ : Finset Q) : Set Q))).map (Subalgebra.toSubmodule (Algebra.adjoin k (T : Set Q))).mkQ :=
        Submodule.span_le.2 fun t ht' => ⟨σ t, Algebra.subset_adjoin (by
          simp only [Finset.coe_union, Finset.coe_image]
          exact Or.inr ⟨t, ht', rfl⟩), hσ t⟩
      obtain ⟨x, hx, hx'⟩ := h5 (h4 g)
      have h6 : x - ρ.r g 2 0 ∈ Algebra.adjoin k (T : Set Q) := (Submodule.Quotient.eq _).1 hx'
      have h7 := sub_mem (show x ∈ Algebra.adjoin k ((T ∪ T'.image σ : Finset Q) : Set Q) from hx) (hle h6)
      rwa [sub_sub_cancel] at h7

theorem UpperTheory.V.Fr.finrank_frameSpace_eq :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ringKrullDim (S.A ⧸ (S.x0 ⊔ S.u.triM)) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨f, h1, h2, h3⟩ := frame_fiber_eq hF hn S (S.x0 ⊔ S.u.triM) le_sup_left
  letI : Algebra (ResidueField O) (S.A ⧸ (S.x0 ⊔ S.u.triM)) := f.toAlgebra
  have ht : (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).triM = ⊥ := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨g, i, j, h, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
  obtain ⟨T, h4, h5⟩ := point hF hn _ _ h1 ht h2
  refine dim_gen (ResidueField O) _ T _ h4 (eq_top_iff.2 fun x _ => ?_)
  have h6 : Subring.closure (Set.range f ∪ {x | ∃ g i j, x = (S.u.map (Ideal.Quotient.mk (S.x0 ⊔ S.u.triM))).r g i j}) ≤
      (Algebra.adjoin (ResidueField O) (T : Set (S.A ⧸ (S.x0 ⊔ S.u.triM)))).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨g, i, j, rfl⟩)
    · exact Subalgebra.algebraMap_mem _ a
    · exact h5 g i j
  exact h6 (h3 ▸ Subring.mem_top x)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_dim {K : Type} [Field K] (W : Submodule K (Fin 2 → K))
    (hE : ∀ v ∈ W, (![v 0, 0] : Fin 2 → K) ∈ W) (a b : Matrix (Fin 2) (Fin 2) K)
    (ha : ∀ v ∈ W, a *ᵥ v ∈ W) (hb : ∀ v ∈ W, b *ᵥ v ∈ W) (ha' : a 1 0 ≠ 0) (hb' : b 0 1 ≠ 0) :
    W = ⊥ ∨ W = ⊤ := by
  have h0 : ∀ v ∈ W, v 0 ≠ 0 → (![1, 0] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 0)⁻¹ (hE v hv) using 1
    ext i; fin_cases i <;> simp [h]
  have h1 : ∀ v ∈ W, v 1 ≠ 0 → (![0, 1] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 1)⁻¹ (W.sub_mem hv (hE v hv)) using 1
    ext i; fin_cases i <;> simp [h, vecHead, vecTail]
  have h01 : (![1, 0] : Fin 2 → K) ∈ W → (![0, 1] : Fin 2 → K) ∈ W := fun h =>
    h1 _ (ha _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using ha')
  have h10 : (![0, 1] : Fin 2 → K) ∈ W → (![1, 0] : Fin 2 → K) ∈ W := fun h =>
    h0 _ (hb _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hb')
  rw [or_iff_not_imp_left]
  intro hW
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
  have key : (![1, 0] : Fin 2 → K) ∈ W ∧ (![0, 1] : Fin 2 → K) ∈ W := by
    by_cases h : v 0 = 0
    · have h' : v 1 ≠ 0 := fun h' => hv0 (by ext i; fin_cases i <;> simp [h, h'])
      exact ⟨h10 (h1 v hv h'), h1 v hv h'⟩
    · exact ⟨h0 v hv h, h01 (h0 v hv h)⟩
  rw [eq_top_iff]
  intro x _
  convert W.add_mem (W.smul_mem (x 0) key.1) (W.smul_mem (x 1) key.2) using 1
  ext i; fin_cases i <;> simp

theorem UpperTheory.V.Fr.typeE :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (K : Type) [Field K] (f : S.A →+* K), S.u.TE (RingHom.ker f) → MatIrr ⊤ fun g : F.G0 => ((S.u.map f).r g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ F C₀ hF S K _ f hT W hW
  obtain ⟨⟨hP, hM⟩, -, hee⟩ := hT
  obtain ⟨hco, -⟩ := co_B hF (Or.inr rfl) S
  have hid := idem hF (Or.inr rfl) S.B S.A S.u (cone_u hF (Or.inr rfl) S).2 0
  have hspan : ∀ M ∈ Submodule.span S.B (Set.range S.u.r), ∀ v ∈ W,
      ((M.map f).submatrix ![0, 2] ![0, 2]) *ᵥ v ∈ W := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g (Subgroup.mem_top g)
    | zero =>
      intro v _
      rw [Matrix.map_zero _ (map_zero f), Matrix.submatrix_zero]
      simp
    | add x y _ _ hx hy =>
      intro v hv
      convert W.add_mem (hx v hv) (hy v hv) using 1
      rw [← Matrix.add_mulVec]
      congr 1
      ext i j
      exact map_add f _ _
    | smul c x _ hx =>
      intro v hv
      convert W.smul_mem (f (algebraMap S.B S.A c)) (hx v hv) using 1
      rw [← Matrix.smul_mulVec]
      congr 1
      ext i j
      exact map_mul f (algebraMap S.B S.A c) _
  have hodd : ∀ g i j, Odd (w 3 i - w 3 j) → f (S.u.r g i j) = 0 := fun g i j h =>
    hee (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  obtain ⟨g, hg⟩ : ∃ g, f (S.u.r g 2 0) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hP (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  obtain ⟨g', hg'⟩ : ∃ g, f (S.u.r g 0 2) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hM (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  refine two_dim W (fun v hv => ?_) _ _ (hW g (Subgroup.mem_top g)) (hW g' (Subgroup.mem_top g')) hg hg'
  convert hspan _ hid v hv using 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.single]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_of_fin {O D R : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing D]
    [CommRing R] [Algebra O R] [IsCO O R] (f : D →+* R) : ((maximalIdeal R).comap f).IsMaximal := by
  have hk : (maximalIdeal R).comap f = RingHom.ker ((res O R).toRingHom.comp f) := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← res_eq_zero_iff O R]
    rfl
  have hp : ((maximalIdeal R).comap f).IsPrime := Ideal.IsPrime.comap _
  rw [hk] at hp ⊢
  haveI : Finite (D ⧸ RingHom.ker ((res O R).toRingHom.comp f)) :=
    Finite.of_injective _ (RingHom.kerLift_injective _)
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

private theorem flat_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (h : (maximalIdeal O).map (algebraMap O O') = maximalIdeal O') : Module.Flat O O' := by
  have hinj : Function.Injective (algebraMap O O') := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    have hp : (RingHom.ker (algebraMap O O')).IsPrime := RingHom.ker_isPrime _
    have hm := eq_maximalIdeal (hp.isMaximal hne)
    refine IsDiscreteValuationRing.not_a_field O' ?_
    rw [← h, ← hm, Ideal.map_eq_bot_iff_le_ker]
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro z ⟨⟨a, ha⟩, hz⟩
  have h1 : algebraMap O O' a * z = 0 := by rw [← Algebra.smul_def]; exact hz
  refine (mul_eq_zero.1 h1).resolve_left fun h2 => nonZeroDivisors.ne_zero ha (hinj ?_)
  rw [h2, map_zero]

theorem UpperTheory.V.Fr.loc_flat :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (L.ι : S.A →+* L.R).Flat ∧ x.IsMaximal ∧ S.mB ≤ S.π x := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  refine ⟨?_, ?_, ?_⟩
  · have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
    have hD : IsNoetherianRing (TensorProduct O L.O' S.A) := by
      have h1 : IsNoetherianRing (TensorProduct O S.A L.O') :=
        Algebra.FiniteType.isNoetherianRing S.A _
      exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv
    let ι' : TensorProduct O L.O' S.A →ₐ[L.O'] L.R :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) L.ι fun _ _ => Commute.all _ _
    have hι : ∀ a, ι' (1 ⊗ₜ a) = L.ι a := fun a => by simp [ι']
    have hc := loc_cpl hF hn S x L ι' hι
    haveI := max_of_fin (O := L.O') ι'.toRingHom
    have h1 : ι'.toRingHom.Flat := (@UpperTheory.V.CA.c3a _ _ _ _ _ ι'.toRingHom.toAlgebra _ _ _ hc).1
    haveI : Module.Flat O L.O' := flat_dvr L.unr
    have h2 : (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom.Flat := by
      have h3 : (algebraMap S.A (TensorProduct O S.A L.O')).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
      have h4 := h3.comp (RingHom.Flat.of_bijective (f := (Algebra.TensorProduct.comm O S.A L.O').toRingEquiv.toRingHom)
        (Algebra.TensorProduct.comm O S.A L.O').bijective)
      exact h4
    have e : (L.ι : S.A →+* L.R) = ι'.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := O) (A := L.O') (B := S.A)).toRingHom :=
      RingHom.ext fun a => (hι a).symm
    rw [e]
    exact h2.comp h1
  · rw [← L.lies]
    exact max_of_fin (O := L.O') _
  · obtain ⟨h, hm⟩ := co_B hF hn S
    have h1 := max_of_fin (O := L.O') ((L.ι : S.A →+* L.R).comp (S.inc : S.B →+* S.A))
    rw [← Ideal.comap_comap, L.lies] at h1
    rw [← hm]
    exact (eq_maximalIdeal h1).ge
end
