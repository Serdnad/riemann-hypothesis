module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem theta_entry {R : Type} [CommRing R] (g : GL (Fin 3) R) (i j : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) i j = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) j.rev i.rev := by
  rw [theta_val]
  simp [Matrix.mul_apply, Jmat]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · simp

private theorem der_inv {O R Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q]
    (x : R →ₐ[O] O) (D : R →ₗ[O] Q) (hD : D ∈ PtDer x Q) (t : Oˣ) (g : GL (Fin 3) R)
    (hg : GeneralLinearGroup.map (x : R →+* O) g = tor O t) (p q : Fin 3) :
    D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      (-((((t ^ wt1 q)⁻¹ : Oˣ) : O) * (((t ^ wt1 p)⁻¹ : Oˣ) : O))) • D ((g : Matrix (Fin 3) (Fin 3) R) p q) := by
  have hDm : ∀ f h : R, D (f * h) = x f • D h + x h • D f := hD
  have hD1 : D 1 = 0 := by
    have h := hDm 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h' : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hx : ∀ i j, x ((g : Matrix (Fin 3) (Fin 3) R) i j) =
      ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg]
    rfl
  have hxi : ∀ i j, x (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i j) =
      (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg, ← map_inv]
    rfl
  have htor : ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => ((t ^ wt1 i : Oˣ) : O) := rfl
  have htori : (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => (((t ^ wt1 i)⁻¹ : Oˣ) : O) := rfl
  have h1 : D ((1 : Matrix (Fin 3) (Fin 3) R) p q) = 0 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact hD1
    · exact map_zero D
  have key := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => D (M p q))
    (congrArg (fun h : GL (Fin 3) R => (h : Matrix (Fin 3) (Fin 3) R)) (mul_inv_cancel g))

  simp only [Units.val_mul, Units.val_one, h1, Matrix.mul_apply, map_sum, hDm, hx, hxi, htor, htori,
  Finset.sum_add_distrib, diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq',
  Finset.mem_univ, if_true] at key
  have e : ((t ^ wt1 p : Oˣ) : O) • D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      -((((t ^ wt1 q)⁻¹ : Oˣ) : O) • D ((g : Matrix (Fin 3) (Fin 3) R) p q)) :=
    eq_neg_of_add_eq_zero_left key
  calc D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q)
      = (((t ^ wt1 p)⁻¹ : Oˣ) : O) • ((t ^ wt1 p : Oˣ) : O) •
          D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by
        rw [e, smul_neg, smul_smul, neg_smul, mul_comm (((t ^ wt1 q)⁻¹ : Oˣ) : O)]

private theorem map_left_eq_tor_and_right_eq_of_map_eq {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (s : ℤˣ) (t : Oˣ) (x : R →ₐ[O] O) (y : GG (m := 3) (R := R))
    (hy : GG.map (x : R →+* O) y = ⟨tor O t, s⟩) :
    GeneralLinearGroup.map (x : R →+* O) y.left = tor O t ∧ y.right = s := by
  constructor
  · have h := congrArg SemidirectProduct.left hy
    simpa [GG.map] using h
  · have h := congrArg SemidirectProduct.right hy
    simpa [GG.map] using h

private theorem wt_rev_rev_eq_wt1_sub_wt1 (i j : Fin 3) : wt j.rev i.rev = wt1 i - wt1 j := by
  fin_cases i <;> fin_cases j <;> decide

theorem UpperTheory.exists_pointDerivation_emb_entry_eq_smul_mat_entry :
    ∀ {O : Type} [CommRing O] (s : ℤˣ) (t : Oˣ) (a b : Fin 3 ⊕ Fin 3), ∃ (u : O) (a' b' : Fin 3), wt a' b' = wt6 a - wt6 b ∧
          ∀ {R Q : Type} [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (x : R →ₐ[O] O),
            ∀ D ∈ PtDer x Q, ∀ y : GG (m := 3) (R := R),
            GG.map (x : R →+* O) y = ⟨tor O t, s⟩ → D (emb y a b) = u • D (y.mat a' b') := by
  intro O _ s t a b
  by_cases hs : s = 1
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp [GG.mat]
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp only [fromBlocks_apply₂₂]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp [GG.mat]
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp only [fromBlocks_apply₂₁]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem one_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) :
    (1 : R) ∈ entMon r 0 :=
  ⟨[], rfl, rfl⟩

private theorem mul_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) {i j : ℤ} {a b : R}
    (ha : a ∈ entMon r i) (hb : b ∈ entMon r j) : a * b ∈ entMon r (i + j) := by
  obtain ⟨L, rfl, rfl⟩ := ha
  obtain ⟨M, rfl, rfl⟩ := hb
  exact ⟨L ++ M, by simp, by simp⟩

private theorem mat_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (g : G) (a b : Fin 3) :
    (r g).mat a b ∈ entMon r (wt1 a - wt1 b) :=
  ⟨[(g, a, b)], by simp [wt], by simp⟩

private theorem theta_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) :
    (theta (r g).left : Matrix (Fin 3) (Fin 3) R) = (r (c * g)).mat := by
  have h : (r c).left = 1 := Units.ext h2
  rw [map_mul, GG.mat, SemidirectProduct.mul_left, h, h1, one_mul, sgnAct_neg_one]

private theorem emb_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R]
    (r : G →* GG (m := 3) (R := R)) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (r g) a b ∈ Submodule.span O (entMon r (wt6 a - wt6 b)) := by
  rw [emb_apply, theta_left r c h1 h2]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact Submodule.zero_mem _
    | exact Submodule.subset_span (mat_mem_entMon r _ a b)

theorem UpperTheory.exists_span_entMon_approx_of_mem_wtPart :
    ∀ {O G R σ : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] [Finite σ]
      (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG (m := 3) (R := R)) (c : G),
          (r c).right = -1 → (r c).mat = 1 → ∀ (w : σ → ℤ) (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R), (∀ s, Φ (MvPowerSeries.X s) ∈ m) →
          (∀ s, ∃ g a b, w s = wt6 a - wt6 b ∧ Φ (MvPowerSeries.X s) =
            emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) →
          ∀ j, ∀ F ∈ wtPart O w j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon r j), Φ F - y ∈ m ^ n := by
  intro O G R σ _ _ _ _ _ η Ψ r c h1 h2 w Φ m hm hX j F hF n
  refine approx w Φ m (fun j => Submodule.span O (entMon r j))
    (Submodule.subset_span (one_mem_entMon r)) ?_ hm ?_ j F hF n
  · intro i j a ha b hb
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_entMon r hx hy
  · intro s
    obtain ⟨g, a, b, hw, he⟩ := hX s
    rw [hw, he]
    refine Submodule.sub_mem _ (emb_mem r c h1 h2 g a b) ?_
    by_cases h : wt6 a = wt6 b
    · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_entMon r))
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b h, map_zero]
      exact Submodule.zero_mem _
end

section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.U3

section Quot

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

private theorem glift_map_map {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R']
    [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R) (f : R →ₐ[O] R')
    (f' : R' →ₐ[O] R'') : (r.map f).map f' = r.map (f'.comp f) := GLift.ext rfl

private theorem univ_quot {P Q : GCond O η Ψ} (V : Univ P) (J : Ideal V.R)
    (hQP : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R), Q R r → P R r)
    (hJ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (f : V.R →ₐ[O] R),
      Q R (V.r.map f) ↔ J ≤ RingHom.ker f)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : Q R₀ r₀) :
    Nonempty (Univ Q) := by
  obtain ⟨f₀, hf₀, -⟩ := (V.rep R₀).2 r₀ (hQP _ _ h₀)
  have hle : J ≤ RingHom.ker f₀ := (hJ R₀ f₀).1 (hf₀ ▸ h₀)
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top f₀ (top_le_iff.1 (h ▸ hle))
  haveI : Nontrivial (V.R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (V.R ⧸ J) :=
    co_quot O V.R (V.R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  refine ⟨⟨V.R ⧸ J, V.r.map (Ideal.Quotient.mkₐ O J), fun R' _ _ _ => ⟨fun f => ?_, fun r' hr' => ?_⟩⟩⟩
  · rw [glift_map_map, hJ]
    intro y hy
    show f (Ideal.Quotient.mk J y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  · obtain ⟨f, hf, hu⟩ := (V.rep R').2 r' (hQP _ _ hr')
    have hk : J ≤ RingHom.ker f := (hJ R' f).1 (hf ▸ hr')
    have hc : (Ideal.Quotient.liftₐ J f hk).comp (Ideal.Quotient.mkₐ O J) = f := AlgHom.ext fun _ => rfl
    refine ⟨Ideal.Quotient.liftₐ J f hk, ?_, fun g hg => ?_⟩
    · show (V.r.map _).map _ = r'
      rw [glift_map_map, hc, hf]
    · have hg' : g.comp (Ideal.Quotient.mkₐ O J) = f := hu _ ((glift_map_map V.r _ g).symm.trans hg)
      exact Ideal.Quotient.algHom_ext O (hg'.trans hc.symm)

private theorem univ_norm {P : GCond O η Ψ} (V : Univ P) (c g₁ : Γ)
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : NormCond c g₁ P R₀ r₀) :
    Nonempty (Univ (NormCond c g₁ P)) := by
  refine univ_quot V (Ideal.span ({x | ∃ a b, x = ((V.r.hom c).mat - 1) a b} ∪
    {zmat c g₁ V.r.hom 0 1, zmat c g₁ V.r.hom 1 0})) (fun _ _ _ _ _ h => h.2) (fun R _ _ _ f => ?_) r₀ h₀
  have hz : ∀ a b, zmat c g₁ (V.r.map f).hom a b = f (zmat c g₁ V.r.hom a b) := fun a b => by
    simp only [zmat, Matrix.sub_apply, map_sub]
    rfl
  have hc : ∀ a b, (((V.r.map f).hom c).mat - 1) a b = f (((V.r.hom c).mat - 1) a b) := fun a b => by
    simp only [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite f, map_one, map_zero]
    rfl
  rw [Ideal.span_le]
  constructor
  · rintro ⟨hn, -⟩ x hx
    show f x = 0
    rcases hx with ⟨a, b, rfl⟩ | rfl | rfl
    · rw [← hc, hn.atc, sub_self, Matrix.zero_apply]
    · rw [← hz, hn.z12]
    · rw [← hz, hn.z21]
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, (V.rep R).1 f⟩
    · rw [← sub_eq_zero]
      ext a b
      rw [hc]
      exact h (Or.inl ⟨a, b, rfl⟩)
    · rw [hz]
      exact h (Or.inr (Or.inl rfl))
    · rw [hz]
      exact h (Or.inr (Or.inr rfl))

private theorem univ_box {H : Type} [Group H] [TopologicalSpace H] {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R)
    (V : Univ (Kills (O := O) (η := η) (Ψ := Ψ) N))
    {R₀ : Type} [CommRing R₀] [Algebra O R₀] [IsCO O R₀] (r₀ : GLift O η Ψ R₀) (h₀ : BoxCond N ι hι U I R₀ r₀) :
    Nonempty (Univ (BoxCond N ι hι U I)) := by
  obtain ⟨φ, hφ, -⟩ := (U.rep V.R).2 (V.r.comap ι hι) trivial
  refine univ_quot V (I.map φ) (fun _ _ _ _ _ h => h.1) (fun R _ _ _ f => ?_) r₀ h₀
  have hf : U.r.map (f.comp φ) = (V.r.map f).comap ι hι := by
    rw [← glift_map_map, hφ]
    exact GLift.ext rfl
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · rintro ⟨-, f', hf', hI⟩
    obtain ⟨g, -, hu⟩ := (U.rep R).2 ((V.r.map f).comap ι hι) trivial
    have e : f' = f.comp φ := (hu f' hf').trans (hu _ hf).symm
    subst e
    exact fun y hy => hI hy
  · exact fun h => ⟨(V.rep R).1 f, f.comp φ, hf, fun y hy => h hy⟩

end Quot

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_sRing :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
      {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} (hι : Continuous ι)
      (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) (cc g₁ : Γ), Marks η Ψ cc g₁ → LocGood U I →
      (∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) → (∀ g ∈ N, r0 η Ψ g = 1) →
      Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) →
      Nonempty (Univ (BoxCond N ι hι U I)) ∧ Nonempty (SRing N hι U I cc g₁) := by
  intro O _ _ _ _ _ Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ hM hL hΨ hN ⟨V⟩
  obtain ⟨x, τ, _, w, φ, hx, hφ, -⟩ := hL.chart
  have h₀ : BoxCond N ι hι U I O (baseLift O η Ψ hΨ) := by
    refine ⟨hN, x, GLift.ext hx, fun y hy => ?_⟩
    have h1 : φ y = 0 := by
      rw [← hφ.ker] at hy
      exact hy
    have h2 := hφ.const y
    rw [h1, map_zero] at h2
    exact IsFractionRing.injective O (FractionRing O) (h2.symm.trans (map_zero _).symm)
  obtain ⟨B⟩ := univ_box hι U I V _ h₀
  exact ⟨⟨B⟩, univ_norm B cc g₁ (baseLift O η Ψ hΨ) ⟨baseRepGL3_normalised_of_psi_eq_one η Ψ g₁ hM.Ψc, h₀⟩⟩
end
