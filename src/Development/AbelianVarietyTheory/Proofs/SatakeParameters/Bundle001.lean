module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Continuity
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

section

namespace GlobalTheory

open scoped BigOperators

theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
end

section

namespace GlobalTheory.CommonEigenvalueAdjoin

theorem exists_common_eigenvalue_of_mem_adjoin {M : Type} [AddCommGroup M] [Module ℂ M]
    (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact ⟨r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨l + m, by rw [LinearMap.add_apply, h1, h3, add_smul],
      by rw [LinearMap.add_apply, h2, h4, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨m * l, by rw [Module.End.mul_apply, h3, map_smul, h1, smul_smul],
      by rw [Module.End.mul_apply, h4, map_smul, h2, smul_smul]⟩

end GlobalTheory.CommonEigenvalueAdjoin
end

section

namespace GlobalTheory.NormBoundTheorem

theorem main : ∀ (M ι T : Type) [inst : AddCommGroup T] [inst_1 : Module ℚ T] (Y : ι → M → ℚ) (t : ι → T), (∀ (s : Finset ι) (c : ι → ℚ), ∑ i ∈ s, c i • Y i = (0 : M → ℚ) → ∑ i ∈ s, c i • t i = (0 : T)) → ∃ (Ξ : (M → ℚ) →+ T), ∀ (i : ι), (Ξ : (M → ℚ) → T) (Y i) = t i := by
  intro M ι T _ _ Y t h
  classical
  let L : (ι →₀ ℚ) →ₗ[ℚ] (M → ℚ) := Finsupp.linearCombination ℚ Y
  let L' : (ι →₀ ℚ) →ₗ[ℚ] T := Finsupp.linearCombination ℚ t
  have hker : LinearMap.ker L ≤ LinearMap.ker L' := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp only [L, L', Finsupp.linearCombination_apply, Finsupp.sum] at hx ⊢
    exact h x.support (fun i => x i) hx
  let g0 : LinearMap.range L →ₗ[ℚ] T :=
    ((LinearMap.ker L).liftQ L' hker).comp (L.quotKerEquivRange.symm : LinearMap.range L →ₗ[ℚ] _)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend g0
  refine ⟨g.toAddMonoidHom, fun i => ?_⟩
  have hmem : Y i ∈ LinearMap.range L := ⟨Finsupp.single i 1, by simp [L]⟩
  have h1 : g (Y i) = g0 ⟨Y i, hmem⟩ := by
    rw [← hg]; rfl
  show g (Y i) = t i
  rw [h1]
  have h2 : (⟨Y i, hmem⟩ : LinearMap.range L) = ⟨L (Finsupp.single i 1), LinearMap.mem_range_self L _⟩ := by
    ext1; simp [L]
  rw [h2]
  simp only [g0, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply]
  simp [L']

end GlobalTheory.NormBoundTheorem
end

section

namespace GlobalTheory.ProdFinCastLE

theorem prod_fin_eq_prod_castLE {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  symm
  rw [show (∏ r : Fin a, f (Fin.castLE h r)) =
      ∏ x ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, f x by
    rw [Finset.prod_map]
    rfl]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hf x ?_
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

end GlobalTheory.ProdFinCastLE
end

section

namespace GlobalTheory.SatakeMainTheorem

theorem main {K : Type} [Field K] (W : Submodule K (Fin (1 : ℕ) → K)) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp h
    have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simpa using h0
    rw [eq_top_iff]
    intro w _
    have hw : w = (w 0 / v 0) • v := by
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [div_mul_cancel₀ _ h0]
    rw [hw]
    exact W.smul_mem _ hv

end GlobalTheory.SatakeMainTheorem
end

section

namespace GlobalTheory

theorem span_map_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L)
    {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ →
    Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓
      Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  intro k _ L _ f a W₁ W₂ h
  have hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw2 : (w : Fin a → k) ∈ W₂ := by
      simpa [Submodule.Quotient.mk_eq_zero] using hw
    have hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂ := ⟨w.2, hw2⟩
    rw [h] at hw12
    exact Subtype.ext (by simpa using hw12)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ
  have hp1 : ∀ w ∈ W₁, p w = w := by
    intro w hw
    have := LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)
    have h2 : g (W₂.mkQ w) = ⟨w, hw⟩ := by simpa using this
    simp only [p, LinearMap.comp_apply, h2]
    rfl
  have hp2 : ∀ w ∈ W₂, p w = 0 := by
    intro w hw
    have h2 : W₂.mkQ w = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using hw
    simp [p, h2]
  let P : (Fin a → L) →ₗ[L] (Fin a → L) := Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)
  have hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v) := by
    intro v
    funext i
    have := RingHom.map_mulVec f (LinearMap.toMatrix' p) v i
    simpa [P, LinearMap.toMatrix'_mulVec] using this.symm
  have hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x := by
    intro x hx
    have heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.id_apply]
      rw [hP, hp1 v hv]
    exact LinearMap.eqOn_span heq hx
  have hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0 := by
    intro x hx
    have heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.zero_apply]
      rw [hP, hp2 v hv]
      funext i
      simp
    exact LinearMap.eqOn_span heq hx
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hx1, hx2⟩
  rw [← hS1 x hx1, hS2 x hx2]

end GlobalTheory
end

section

namespace GlobalTheory.HeckeCorr

variable {Gf : Type*} [Group Gf]

def heckeLevel (U : Subgroup Gf) (g : Gf) : Subgroup Gf := U ⊓ U.map (MulAut.conj g).toMonoidHom

theorem heckeLevel_le (U : Subgroup Gf) (g : Gf) : heckeLevel U g ≤ U := inf_le_left

theorem conj_mem_of_mem_heckeLevel {U : Subgroup Gf} {g u : Gf} (hu : u ∈ heckeLevel U g) : g⁻¹ * u * g ∈ U := by
  obtain ⟨-, v, hv, rfl⟩ := hu
  simpa [MulAut.conj_apply, mul_assoc] using hv

end GlobalTheory.HeckeCorr
end

section

set_option autoImplicit false

open CategoryTheory

universe v u

namespace GlobalTheory.CatH.DSq

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

theorem sign_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℤ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

end GlobalTheory.CatH.DSq
end

section

namespace GlobalTheory.ExistsRepresentation

theorem exists_represent {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v : V, v ≠ 0 → (0 : ℝ) < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  classical
  let b := Module.finBasis ℂ W
  let Φ : W →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun u i => Bf (u : V) (b i : V)
      map_add' := by
        intro u u'
        funext i
        simp
      map_smul' := by
        intro c u
        funext i
        simp }
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ w : W, Bf (u : V) (w : V) = 0 := by
      intro w
      rw [← b.sum_repr w]

      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smulₛₗ]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 := congrFun hu i
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
      simp [h0]
    by_contra hne
    have hne' : (u : V) ≠ 0 := by simpa using hne
    have h1 := hpos _ hne'
    rw [hall u] at h1
    simp at h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨u, hu⟩ := hsurj (fun i => L (b i : V))
  refine ⟨u, u.2, fun w hw => ?_⟩
  have hwsum : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V) := by
    have h2 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  rw [hwsum]

  simp only [map_sum, map_smulₛₗ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h3 := congrFun hu i
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h3
  rw [h3]

end GlobalTheory.ExistsRepresentation
end

section

namespace GlobalTheory.NormAevalSubBound

theorem norm_aeval_sub_le {k : Type} [inst : NormedField k] [NormOneClass k] [IsUltrametricDist k]
    {J : Type} {x y : J → k} {δ : ℝ} (hδ : (0 : ℝ) ≤ δ) (hx : ∀ (j : J), ‖x j‖ ≤ (1 : ℝ))
    (hy : ∀ (j : J), ‖y j‖ ≤ (1 : ℝ)) (hxy : ∀ (j : J), ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P -
      (MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ δ := by
  have hadd : ∀ (a b : k) (r : ℝ), ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a + b‖ ≤ r := fun a b r ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : ‖(a : k)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one k a
    refine ⟨?_, ?_, ?_⟩
    · simpa using h
    · simpa using h
    · simpa using hδ
  | add p q hp hq =>
    obtain ⟨p1, p2, p3⟩ := hp
    obtain ⟨q1, q2, q3⟩ := hq
    simp only [map_add (f := _)]
    refine ⟨hadd _ _ _ p1 q1, hadd _ _ _ p2 q2, ?_⟩
    rw [add_sub_add_comm]
    exact hadd _ _ _ p3 q3
  | mul_X p j hp =>
    obtain ⟨p1, p2, p3⟩ := hp
    simp only [map_mul, MvPolynomial.aeval_X]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]; exact mul_le_one₀ p1 (norm_nonneg _) (hx j)
    · rw [norm_mul]; exact mul_le_one₀ p2 (norm_nonneg _) (hy j)
    · have e : MvPolynomial.aeval x p * x j - MvPolynomial.aeval y p * y j =
          MvPolynomial.aeval x p * (x j - y j) +
            (MvPolynomial.aeval x p - MvPolynomial.aeval y p) * y j := by ring
      rw [e]
      refine hadd _ _ _ ?_ ?_
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) p1).trans (hxy j)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hy j)).trans p3

end GlobalTheory.NormAevalSubBound
end
