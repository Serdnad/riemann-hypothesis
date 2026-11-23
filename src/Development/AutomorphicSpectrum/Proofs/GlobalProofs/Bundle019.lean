module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle413
public import GroundTheory.AutomorphicForms.FiniteLength
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacquetBlocks

namespace GlobalTheory.CompanionTheory.JacquetBridge

section Bridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eq_iff_of_lt_iff {ι A B : Type} [LinearOrder A] [LinearOrder B] {f : ι → A} {g : ι → B}
    (h : ∀ i j, f i < f j ↔ g i < g j) (i j : ι) : f i = f j ↔ g i = g j := by
  constructor
  · intro hf
    refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
    · exact (lt_irrefl (f i)) (by simpa [hf] using (h j i).2 hlt)
    · exact (lt_irrefl (f i)) (by simpa [hf] using (h i j).2 hlt)
  · intro hg
    refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
    · exact (lt_irrefl (g i)) (by simpa [hg] using (h j i).1 hlt)
    · exact (lt_irrefl (g i)) (by simpa [hg] using (h i j).1 hlt)

theorem mem_blockUpper_iff (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (g : GL (Fin N) k) :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N β ↔ g ∈ parab k e := by
  show (g : Matrix (Fin N) (Fin N) k).BlockTriangular β ↔ (g : Matrix (Fin N) (Fin N) k).BlockTriangular (blk e)
  exact ⟨fun h i j hij => h ((hβ j i).2 hij), fun h i j hij => h ((hβ j i).1 hij)⟩

theorem mem_unipotentRadical_iff (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (g : GL (Fin N) k) :
    g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β ↔ g ∈ unipRad k e := by
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, mem_unipRad_iff_blk, mem_blockUpper_iff e hβ]
  exact and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j =>
    imp_congr_left (eq_iff_of_lt_iff hβ i j))

def leviMap (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) :
    Levi k m →* GroundTheory.Automorphic.Parabolic.levi k N β :=
  (leviEmb k e).codRestrict _ fun g => GroundTheory.Automorphic.Parabolic.mem_levi.2 fun i j hij =>
    leviEmb_apply_of_blk_ne e g fun h => hij ((eq_iff_of_lt_iff hβ i j).2 h)

theorem leviMap_surjective (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) :
    Function.Surjective (leviMap (k := k) e hβ) := by
  intro x
  let p : parab k e :=
    ⟨x, (mem_blockUpper_iff e hβ _).1 (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper x.2)⟩
  have hoff : ∀ i j, blk e i ≠ blk e j → ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 :=
    fun i j hij => GroundTheory.Automorphic.Parabolic.mem_levi.1 x.2 i j
      (fun h => hij ((eq_iff_of_lt_iff hβ i j).1 h))
  exact ⟨leviProj k e p, Subtype.ext (leviEmb_leviProj_of_blk e p hoff)⟩

theorem hasFiniteLength_of_twist {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (χ : G →* ℂ) (σ : Representation ℂ G W)
    (h : HasFiniteLength (GroundTheory.Automorphic.Parabolic.twist χ σ)) : HasFiniteLength σ := by
  have heq : GroundTheory.Automorphic.Parabolic.twist χ σ = GlobalTheory.SmGL.twist σ χ.toHomUnits := by
    ext g v
    rfl
  rw [heq] at h
  exact (hasFiniteLength_twist_iff σ χ.toHomUnits).1 h

theorem hasFiniteLength_jacU_of_labelling (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (π : Representation ℂ (GL (Fin N) k) V)
    (h : HasFiniteLength (GroundTheory.Automorphic.Parabolic.jacquetRep k N β π)) :
    HasFiniteLength (jacU e π) := by
  have h1 : HasFiniteLength (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π) :=
    hasFiniteLength_of_twist
      ((GroundTheory.Automorphic.Parabolic.invSqrtModular k N β).comp GroundTheory.Automorphic.Parabolic.leviIncl) _ h
  have h2 : HasFiniteLength ((GroundTheory.Automorphic.Parabolic.jacquetAction k N β π).comp (leviMap e hβ)) :=
    (hasFiniteLength_comp_iff _ _ (leviMap_surjective e hβ)).2 h1
  have hU : ∀ u : GL (Fin N) k, u ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β → u ∈ unipRad k e :=
    fun u hu => (mem_unipotentRadical_iff e hβ u).1 hu
  let f : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π →ₗ[ℂ] V ⧸ twKer π (unipRad k e) 1 :=
    Representation.Coinvariants.lift _ (twKer π (unipRad k e) 1).mkQ (fun u => by
      ext v
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hU u u.2⟩, v, by simp⟩)
  let Φ : Representation.IntertwiningMap ((GroundTheory.Automorphic.Parabolic.jacquetAction k N β π).comp (leviMap e hβ))
      (jacU e π) :=
    ⟨f, fun g => by
      refine Representation.Coinvariants.hom_ext ?_
      ext v
      rfl⟩
  refine hasFiniteLength_of_surjective Φ ?_ h2
  intro y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (twKer π (unipRad k e) 1) y
  exact ⟨Representation.Coinvariants.mk _ v, rfl⟩

end Bridge

theorem jacquetFiniteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e V _ _ π hπ hfl
  show HasFiniteLength (GlobalTheory.SmGL.twist (jacU e π) (deltaHalf k m)⁻¹)
  rw [hasFiniteLength_twist_iff]
  let ψ : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let e0 : (Σ a, m a) ≃ Fin (Fintype.card n) := e.trans ψ.symm
  have he : e0.trans ψ = e := by
    ext x
    simp [e0]
  rw [← he]
  apply hasFiniteLength_jacU_reindex e0 ψ π
  let o : α ≃o Fin (Fintype.card α) := (Fintype.orderIsoFinOfCardEq α rfl).symm
  let β : Fin (Fintype.card n) → ℕ := fun i => (o (blk e0 i) : ℕ)
  have hβ : ∀ i j, β i < β j ↔ blk e0 i < blk e0 j := fun i j => by
    show (o (blk e0 i) : ℕ) < (o (blk e0 j) : ℕ) ↔ _
    rw [← Fin.lt_def]
    exact o.lt_iff_lt
  refine hasFiniteLength_jacU_of_labelling e0 hβ _ ?_
  refine GroundTheory.Automorphic.Parabolic.hasFiniteLength_jacquetRep ?_ ?_ β
  · intro v
    have hcont : Continuous (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv) := by
      show Continuous (Units.map (Matrix.reindexAlgEquiv k k ψ).toMulEquiv.toMonoidHom)
      exact Units.continuous_map (continuous_id.matrix_reindex ψ ψ)
    have hset : (GroundTheory.Automorphic.stabilizerOf
        (π.comp (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom) v :
          Set (GL (Fin (Fintype.card n)) k)) =
        (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv) ⁻¹' {g | π g v = v} := by
      ext g
      exact GroundTheory.Automorphic.mem_stabilizerOf
    rw [hset]
    exact (hπ v).preimage hcont
  · exact (hasFiniteLength_comp_iff π _ (MulEquiv.surjective _)).2 hfl

end GlobalTheory.CompanionTheory.JacquetBridge

end
end

section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_prod_fin {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (r : ℕ) :
    Summable (fun m : Fin r → ℕ => ∏ i, f (m i)) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h2 := Summable.mul_of_nonneg hf ih (fun n => h0 n)
      (fun m => Finset.prod_nonneg fun i _ => h0 (m i))
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]
    convert h2 using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

private theorem exists_pos_lower_bound_of_forall_pos {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ (∀ j, c ≤ b j) ∧ ∀ j i, c ≤ a j i := by
  classical
  let T : Finset ℝ := Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩
    · have h := T.min'_mem hT
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩
      · rw [← hj]; exact hb j
      · rw [← hj]; exact ha j i
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  · refine ⟨1, one_pos, fun j => ?_, fun j i => ?_⟩
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT

theorem coneTerm_summable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re →
    Summable (coneTerm a b s) := by
  intro ι _ r a b hr ha hb s hs
  obtain ⟨c, hc0, hcb, hca⟩ := exists_pos_lower_bound_of_forall_pos a b ha hb
  have hσ0 : 0 < s.re := by linarith
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι := pow_nonneg (Real.rpow_nonneg hc0.le _) _
  have hg := (summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left
    ((c ^ (-s.re)) ^ Fintype.card ι)
  have key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re) := fun hx hxy => by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 < S := by linarith
  have hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ) := by
    intro j
    rw [hSdef, mul_add, mul_one, Finset.mul_sum]
    apply add_le_add (hcb j)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)
  have hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ) := fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)
  have hv1 : S ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)
  have hv0 : 0 ≤ S ^ (-s.re) := Real.rpow_nonneg hS0.le _
  calc ‖coneTerm a b s m‖ = ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ (-s.re) := by
        rw [coneTerm, norm_prod]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]
    _ ≤ ∏ _j : ι, (c * S) ^ (-s.re) :=
        Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (hLpos j).le _)
          (fun j _ => key (mul_pos hc0 hS0) (hL j))
    _ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC
    _ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod₀ (fun i _ => hv0)
        intro i _
        apply key (by positivity)
        have hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ) :=
          Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)
        rw [hSdef]
        linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem finite_realEmbeddings (F : Type) [Field F] [NumberField F] : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) (by
    intro σ τ h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this)

theorem bounded_ratio_on_basis_cone : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) →
    ∃ R : ℝ, 0 < R ∧ ∀ x : F, (∀ i, 0 < b.repr x i) → ∀ σ τ : F →+* ℝ, σ x ≤ R * τ x := by
  intro F _ _ κ _ b hb
  classical
  haveI := finite_realEmbeddings F
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hterm : ∀ (i : κ) (σ τ : F →+* ℝ), 0 < σ (b i) / τ (b i) := fun i σ τ => div_pos (hb i σ) (hb i τ)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) := ⟨_, rfl⟩
  have hsum : 0 ≤ ∑ i, ∑ σ : F →+* ℝ, ∑ τ : F →+* ℝ, σ (b i) / τ (b i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => (hterm i σ τ).le
  have hR : 0 < R := by rw [hRdef]; linarith
  have hle : ∀ (i : κ) (σ τ : F →+* ℝ), σ (b i) ≤ R * τ (b i) := by
    intro i σ τ
    have h1 : σ (b i) / τ (b i) ≤ ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun τ' : F →+* ℝ => σ (b i) / τ' (b i)) (fun τ' _ => (hterm i σ τ').le) (Finset.mem_univ τ)
    have h2 : ∑ τ' : F →+* ℝ, σ (b i) / τ' (b i) ≤ ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) :=
      Finset.single_le_sum (f := fun σ' : F →+* ℝ => ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i))
        (fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm i σ' τ').le) (Finset.mem_univ σ)
    have h3 : ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b i) / τ' (b i) ≤ ∑ j, ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j) :=
      Finset.single_le_sum (f := fun j => ∑ σ' : F →+* ℝ, ∑ τ' : F →+* ℝ, σ' (b j) / τ' (b j))
        (fun j _ => Finset.sum_nonneg fun σ' _ => Finset.sum_nonneg fun τ' _ => (hterm j σ' τ').le) (Finset.mem_univ i)
    have h4 : σ (b i) / τ (b i) ≤ R := by rw [hRdef]; linarith
    exact (div_le_iff₀ (hb i τ)).1 h4
  refine ⟨R, hR, fun x hx σ τ => ?_⟩
  have hrep : ∀ ρ : F →+* ℝ, ρ x = ∑ i, (b.repr x i : ℝ) * ρ (b i) := by
    intro ρ
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
  rw [hrep σ, hrep τ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc : (0 : ℝ) < (b.repr x i : ℝ) := by exact_mod_cast hx i
  calc (b.repr x i : ℝ) * σ (b i) ≤ (b.repr x i : ℝ) * (R * τ (b i)) := mul_le_mul_of_nonneg_left (hle i σ τ) hc.le
    _ = R * ((b.repr x i : ℝ) * τ (b i)) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem exists_pow_mem_congUnits : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  intro F _ _ 𝔣 h𝔣
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hpos : 0 < Nat.card (𝓞 F ⧸ 𝔣)ˣ := Nat.card_pos
  refine ⟨2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ, by omega, fun u => ⟨?_, fun σ => ?_⟩⟩
  · have h1 : (Units.map (Ideal.Quotient.mk 𝔣 : 𝓞 F →* 𝓞 F ⧸ 𝔣) u) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) = 1 := by
      rw [mul_comm, pow_mul, pow_card_eq_one', one_pow]
    have h2 : Ideal.Quotient.mk 𝔣 ((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) = Ideal.Quotient.mk 𝔣 1 := by
      have h3 := congrArg (fun z : (𝓞 F ⧸ 𝔣)ˣ => (z : 𝓞 F ⧸ 𝔣)) h1
      simpa using h3
    exact Ideal.Quotient.eq.mp h2
  · have hne : σ (((u : 𝓞 F)) : F) ≠ 0 := by
      rw [Ne, map_eq_zero]
      simp
    have h : (((u ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) : (𝓞 F)ˣ) : 𝓞 F) : F) = (((u : 𝓞 F)) : F) ^ (2 * Nat.card (𝓞 F ⧸ 𝔣)ˣ) := by
      simp
    rw [h, map_pow, pow_mul]
    exact pow_pos (by positivity) _

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem embedding_unit_le_abs {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {R : ℝ} {u : (𝓞 F)ˣ}
    (hu : TotPos F ((u : 𝓞 F) : F)) (hR : ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F))
    (σ : F →+* ℝ) : σ ((u : 𝓞 F) : F) ≤ |R| := by
  classical
  haveI : Finite (F →+* ℝ) := Finite.of_equiv _ (realEmbeddingsEquiv F).symm
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hprod : ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) = 1 := by
    rw [prod_real_embeddings_eq_absNorm (u : 𝓞 F) hu, Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top]
    simp
  obtain ⟨τ, hτ⟩ : ∃ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) ≤ 1 := by
    by_contra hne
    push_neg at hne
    have hlt : ∏ _τ : F →+* ℝ, (1 : ℝ) < ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => one_pos) (fun τ _ => hne τ) ⟨σ, Finset.mem_univ σ⟩
    rw [hprod] at hlt
    simp at hlt
  calc σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F) := hR σ τ
    _ ≤ |R| * τ ((u : 𝓞 F) : F) := mul_le_mul_of_nonneg_right (le_abs_self R) (hu τ).le
    _ ≤ |R| * 1 := mul_le_mul_of_nonneg_left hτ (abs_nonneg R)
    _ = |R| := mul_one _

theorem finite_totPos_units_bounded_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  intro F _ _ _ R
  have hinj : Function.Injective (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) := fun a b h =>
    Units.ext (RingOfIntegers.ext h)
  refine ((Embeddings.finite_of_norm_le F ℂ |R|).preimage hinj.injOn).subset ?_
  rintro u ⟨hu, hR⟩
  refine ⟨(u : 𝓞 F).isIntegral_coe, fun φ => ?_⟩
  obtain ⟨σ, rfl⟩ := (realEmbeddingsEquiv F).surjective φ
  have h := embedding_unit_le_abs hu hR σ
  change ‖((σ ((u : 𝓞 F) : F) : ℝ) : ℂ)‖ ≤ |R|
  rw [Complex.norm_real, Real.norm_of_nonneg (hu σ).le]
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.partial_zeta_twisted_entire_difference : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem _root_.GlobalTheory.T.ray_class_cone_parametrization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam <;> assumption)
end

end

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_series_summable_right_half_plane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re → Summable (coneTerm a b s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable <;> assumption)

end
end
