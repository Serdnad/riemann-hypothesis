module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle041
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BurnsideField

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isAlgClosed {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  apply GlobalTheory.BurnsideMonoid.span_range_eq_top_of_isIrreducible <;> assumption

theorem span_mat_eq_top_of_isIrrSub {Γ K : Type} [Group Γ] [Field K] [IsAlgClosed K] {r : ℕ}
    (σ : Γ →* GL (Fin r) K) (h : IsIrrSub σ ⊤) : Submodule.span K (Set.range (mat σ)) = ⊤ := by
  classical
  let τ : Representation K Γ (Fin r → K) :=
    { toFun := fun g => Matrix.toLin' (mat σ g)
      map_one' := by simp [mat]; rfl
      map_mul' := fun g g' => by simp [mat, Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (mat σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      exact (congrArg Subrepresentation.toSubmodule hbt).symm
    refine ⟨fun W => ?_⟩
    rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isAlgClosed τ hirr
  have hm : Set.range (mat σ) = (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (mat σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

theorem span_eq_top_of_span_map {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k)
    (h : Submodule.span K (Set.range fun g => (M g).map (algebraMap k K)) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let F : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
    { toFun := fun X => ∑ i, ∑ j, X i j * algebraMap k K (f (Matrix.single i j 1))
      map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }
  have hF : ∀ X : Matrix (Fin r) (Fin r) k, F (X.map (algebraMap k K)) = algebraMap k K (f X) := by
    intro X
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]

    simp only [map_sum]
    change ∑ i, ∑ j, algebraMap k K (X i j) * algebraMap k K (f (Matrix.single i j 1)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, map_mul]
  have hker : (⊤ : Submodule K (Matrix (Fin r) (Fin r) K)) ≤ LinearMap.ker F := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have : f (M g) = 0 := hf (Submodule.subset_span ⟨g, rfl⟩)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
  apply hf0
  refine LinearMap.ext fun X => ?_
  have h1 : F (X.map (algebraMap k K)) = 0 := hker trivial
  rw [hF] at h1
  exact (algebraMap k K).injective (by rw [h1]; simp)

theorem span_mat_eq_top_of_absIrrSub :
    ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  intro Γ k _ _ r ρ h
  classical
  have htop : Submodule.span (AlgebraicClosure k)
      ((fun v : Fin r → k => (algebraMap k (AlgebraicClosure k)) ∘ v) ''
      ((⊤ : Submodule k (Fin r → k)) : Set (Fin r → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub at h
  rw [htop] at h
  have h2 := span_mat_eq_top_of_isIrrSub _ h
  have h3 : mat (mapRep (algebraMap k (AlgebraicClosure k)) ρ) =
      fun g => (mat ρ g).map (algebraMap k (AlgebraicClosure k)) := by
    funext g
    ext p q
    simp [mat, mapRep]
  rw [h3] at h2
  exact span_eq_top_of_span_map (mat ρ) h2

end GlobalTheory.BurnsideField
end

section

noncomputable section

namespace GlobalTheory.WachSat

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem exists_pow_smul_le {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (c : O) (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L S : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (hS : S.FG) :
    ∃ m : ℕ, ∀ x ∈ S, c ^ m • x ∈ L := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_7 h_8 h_9 h_10; revert LL O h_2 h_3 h_4 h_5 V h_7 h_8 h_9 h_10 c hc L S hL hS; exact @_root_.GlobalTheory.PowerScalarMembership.main)
  | exact @_root_.GlobalTheory.PowerScalarMembership.main
  | exact _root_.GlobalTheory.PowerScalarMembership.main
  | (apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScalarMembership.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScalarMembership.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScalarMembership.main ..)

variable (W : LocWach PD LL O v n)

theorem ee_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (x : W.EE)
    (hx : (PD.p : W.EE) * x = 0) : x = 0 := by
  have hA : ∀ a : LetA O n, (PD.p : LetA O n) * a = 0 → a = 0 := by
    intro a ha
    funext i
    ext k
    have h1 : (PD.p : PowerSeries O) * a i = 0 := congrFun ha i
    have h2 := congrArg (PowerSeries.coeff k) h1
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, map_zero] at h2
    simpa using hp _ h2
  haveI := W.EE_complete
  refine IsHausdorff.haus (I := Ideal.span {((PD.p : ℕ) : W.EE)}) inferInstance x fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨a, m, ha⟩ := W.EE_dense x k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b, hb⟩ := W.EE_sat ((PD.p : LetA O n) * a) (k + 1) (by
    refine Ideal.mem_span_singleton'.2 ⟨-y, ?_⟩
    rw [map_mul, map_natCast]
    linear_combination (-(PD.p : W.EE)) * hy - (algebraMap (LetA O n) W.EE (letπ ^ m)) * hx)
  have hab : a = (PD.p : LetA O n) ^ k * b := by
    have := hA (a - (PD.p : LetA O n) ^ k * b) (by rw [mul_sub, hb]; ring)
    exact sub_eq_zero.1 this
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ m)) := by
    rw [map_pow]; exact W.EE_π.pow m
  refine Ideal.mem_span_singleton'.2 ⟨(y + algebraMap (LetA O n) W.EE b) * ↑u⁻¹, ?_⟩
  rw [hab, map_mul, map_pow (algebraMap (LetA O n) W.EE) (PD.p : LetA O n), map_natCast, ← hu] at hy
  have huu : (u : W.EE) * ↑u⁻¹ = 1 := u.mul_inv
  linear_combination (↑u⁻¹ : W.EE) * hy + x * huu

theorem mem_of_pow_smul_mem (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O)
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T) (m : ℕ) (x : W.DD T)
    (hx : ((PD.p : O) ^ m) • x ∈ W.N T) : x ∈ W.N T := by
  obtain ⟨b, hli, hsp⟩ := hb
  have hxs : x ∈ Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) := hsp ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hxs
  set a := b.repr ⟨_, hx⟩ with ha
  have h1 : ∑ j, algebraMap (LetA O n) W.EE (a j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hx⟩)

    rw [map_sum] at this
    simpa only [algebraMap_smul, map_smul, Submodule.subtype_apply] using this
  have h2 : ∑ j, ((PD.p : W.EE) ^ m * e j) • (b j : W.DD T) = ((PD.p : O) ^ m) • x := by
    rw [← he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, ← algebraMap_smul W.EE ((PD.p : O) ^ m), map_pow, map_natCast]
  have h3 : ∀ j, algebraMap (LetA O n) W.EE (a j) = (PD.p : W.EE) ^ m * e j :=
    Fintype.linearIndependent_iffₛ.1 hli _ _ (h1.trans h2.symm)
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (ee_torsionFree W hp _ (by rw [← hy]; ring))
  have h4 : ∀ j, ∃ c : LetA O n, e j = algebraMap (LetA O n) W.EE c := by
    intro j
    obtain ⟨c, hc⟩ := W.EE_sat (a j) m (Ideal.mem_span_singleton'.2 ⟨e j, by rw [h3, mul_comm]⟩)
    refine ⟨c, sub_eq_zero.1 (hreg m _ ?_)⟩
    have := h3 j
    rw [hc, map_mul, map_pow, map_natCast] at this
    rw [mul_sub, this, sub_self]
  choose c hc using h4
  rw [← he]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hc, algebraMap_smul]
  exact (W.N T).smul_mem _ (b j).2

end Generic

end GlobalTheory.WachSat
end
end

section

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.SenLines.SplitFil

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def lineMap {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) : (Fin r → F⟦X⟧) →ₗ[F] (ℤ → M) where
  toFun c := ∑ k, serLine (u k) (d k) (c k)
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.add_apply]
    split_ifs <;> simp [add_smul]
  map_smul' a c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.smul_apply]
    split_ifs <;> simp [mul_smul]

theorem smul_serMul (a : F) (f : F⟦X⟧) {y : ℤ → M} (hy : IsLaurent y) :
    a • serMul f y = serMul (a • f) y := by
  funext m
  simp only [Pi.smul_apply, serMul]
  rw [smul_finsum' a (serMul_finite f hy m)]
  refine finsum_congr fun j => ?_
  simp [mul_smul]

theorem mem_serSpan_iff {N : Type} (L : N → ℤ → M) (hL : ∀ x, IsLaurent (L x)) (y : ℤ → M) :
    y ∈ serSpan F (Set.range L) ↔
      ∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j)) := by
  constructor
  · intro hy
    obtain ⟨n, c, g, h⟩ := Submodule.mem_span_set'.mp hy
    have hg : ∀ i, ∃ (f : F⟦X⟧) (x : N), (g i : ℤ → M) = serMul f (L x) := fun i => by
      obtain ⟨f, w, ⟨x, rfl⟩, -, h⟩ := (g i).2
      exact ⟨f, x, h⟩
    choose f x hg using hg
    refine ⟨n, x, fun i => c i • f i, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, smul_serMul _ _ (hL _)]
    rfl
  · rintro ⟨s, x, f, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨f j, L (x j), ⟨x j, rfl⟩, hL _, rfl⟩

theorem exists_coef {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (a : ℤ) (z : M)
    (hz : z ∈ Submodule.span F (d '' {k | a ≤ u k})) :
    ∃ c : Fin r → F, (∀ k, u k < a → c k = 0) ∧ z = ∑ k, c k • d k := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun k' hk' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hk (not_le.mpr hk')
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun k hk => by simp [hc k hk, hc' k hk],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul b x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨b • c, fun k hk => by simp [hc k hk], by simp [mul_smul, Finset.smul_sum]⟩

theorem gradedSer_eq_range {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) :
    gradedSer A = LinearMap.range (lineMap (F := F) u d) := by
  apply le_antisymm
  · refine iSup_le fun a y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hex : ∀ m : ℤ, ∃ c : Fin r → F, (∀ k, m + u k < 0 → c k = 0) ∧
        y m = ∑ k, c k • d k := fun m => by
      by_cases hm : m < -a
      · exact ⟨0, fun _ _ => rfl, by simp [hy0 m hm]⟩
      · obtain ⟨c, hc, h⟩ := exists_coef u d a (y m) (hA a ▸ hy1 m)
        exact ⟨c, fun k hk => hc k (by omega), h⟩
    choose c hc hyc using hex
    refine ⟨fun k => PowerSeries.mk fun j => c ((j : ℤ) - u k) k, ?_⟩
    funext m
    change (∑ k, serLine (u k) (d k) (PowerSeries.mk fun j => c ((j : ℤ) - u k) k)) m = y m
    rw [Finset.sum_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold serLine
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc m k (not_le.mp h), zero_smul]
  · rintro _ ⟨c, rfl⟩
    change (∑ k, serLine (u k) (d k) (c k)) ∈ _
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.mem_iSup_of_mem (u k) ⟨fun m hm => ?_, fun m => ?_⟩
    · unfold serLine
      rw [if_neg (by omega)]
    · unfold serLine
      split_ifs
      · rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, le_refl (u k), rfl⟩)
      · exact Submodule.zero_mem _

theorem spanIsLines_of_graded : ∀ {F M N : Type} [Field F] [AddCommGroup M] [Module F M] (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent (L x)) → (∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serSpan F (Set.range L) = GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.gradedSer A → GlobalTheory.SenLines.SpanIsLines L u d F := by
  intro F M N _ _ _ L r u d A hL hA h y
  rw [← mem_serSpan_iff L hL, h, gradedSer_eq_range u d A hA]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end GlobalTheory.SenLines.SplitFil
end
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilRing_mod_high_degree_property : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.RingModHigh O K l e := by
  first | exact @GlobalTheory.BK.ringModHigh | exact GlobalTheory.BK.ringModHigh | (intros; apply GlobalTheory.BK.ringModHigh <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  first | exact @GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | exact GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | (intros; apply GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ r : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ r) D₁.L D₂.L → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsAll F (l ^ r) := by
  first | exact @GlobalTheory.CokerLift.killsAll_of_killsCoker_L | exact GlobalTheory.CokerLift.killsAll_of_killsCoker_L | (intros; apply GlobalTheory.CokerLift.killsAll_of_killsCoker_L <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.lift_image_eulerE_invariants_quotient : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : BKHom D₀ D₁) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D₁ U → ∀ ω : D₁.Pol, (∃ w ∈ D₁.Zl, D₁.Lc w = ω) → ∀ c : ℕ, (∃ w₀ ∈ D₀.Zl, F.onPol w₀ = (l : K) ^ c • ω) → ∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = ω := by
  first | exact @GlobalTheory.Proof.LiftImage.lift_image | exact GlobalTheory.Proof.LiftImage.lift_image | (intros; apply GlobalTheory.Proof.LiftImage.lift_image <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_integrality_computation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  first | exact @GlobalTheory.IntegralityComp.integralityComputation | exact GlobalTheory.IntegralityComp.integralityComputation | (intros; apply GlobalTheory.IntegralityComp.integralityComputation <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.prime_pow_divisibility_of_descentDatum : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  first | exact @GlobalTheory.divisible_of_BKDat | exact GlobalTheory.divisible_of_BKDat | (intros; apply GlobalTheory.divisible_of_BKDat <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  first | exact @GlobalTheory.ZFin.finiteFree_and_localisation | exact GlobalTheory.ZFin.finiteFree_and_localisation | (intros; apply GlobalTheory.ZFin.finiteFree_and_localisation <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  first | exact @GlobalTheory.lagrange_C_rho_eq_comb_degrees | exact GlobalTheory.lagrange_C_rho_eq_comb_degrees | (intros; apply GlobalTheory.lagrange_C_rho_eq_comb_degrees <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem span_matrix_eq_top_of_residue_span {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (f i).map (IsLocalRing.residue A))) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | (apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)

theorem span_mat_eq_top_of_residue {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  span_matrix_eq_top_of_residue_span (mat ρ) h

end GlobalTheory
end
