module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

namespace GlobalTheory

theorem mem_of_semilinear_mem_complex_span : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V), LinearIndependent ℂ (fun k => j (b k)) → ∀ (U : Submodule K V) (x : V), j x ∈ Submodule.span ℂ (j '' (U : Set V)) → x ∈ U := by
  intro K V W ι _ _ _ _ _ _ σ j b hli U x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hxU inferInstance
  obtain ⟨L, hL⟩ := (Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli)
  let g : W →ₗ[ℂ] ℂ := (Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L
  have hb : ∀ k, g (j (b k)) = σ (f (b k)) := by
    intro k
    have h1 : L (j (b k)) = Finsupp.single k 1 := by
      have := LinearMap.congr_fun hL (Finsupp.single k 1)
      simpa using this
    simp [g, h1]
  have hg : ∀ v, g (j v) = σ (f v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]; simp
  have hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have : f u = 0 := by
      have : f u ∈ U.map f := ⟨u, hu, rfl⟩
      rw [hfU] at this
      simpa using this
    simp [hg, this]
  have h0 : σ (f x) = 0 := by rw [← hg]; exact hle hx
  exact hfx (by simpa using h0)

end GlobalTheory
end

section

namespace GlobalTheory.TraceEqualFinrank

open Module

theorem trace_eq_finrank_range {g : ℕ} (P : Matrix (Fin g) (Fin g) ℂ) (hP : IsIdempotentElem P) :
    Matrix.trace P = (finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' P)).mpr he
  rw [← Matrix.trace_toLin'_eq, hproj.trace]

theorem exists_mul_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P')
    (h : Matrix.trace P = Matrix.trace P') :
    ∃ (X : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℂ), Y * P' * X = P := by
  have hrk : finrank ℂ (LinearMap.range (Matrix.toLin' P')) =
      finrank ℂ (LinearMap.range (Matrix.toLin' P)) := by
    have h2 := (trace_eq_finrank_range P' hP').symm.trans (h.symm.trans (trace_eq_finrank_range P hP))
    exact_mod_cast h2
  let e := LinearEquiv.ofFinrankEq _ _ hrk
  have hid' : ∀ w ∈ LinearMap.range (Matrix.toLin' P'), Matrix.toLin' P' w = w := by
    rintro w ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP'.eq]
  let Xl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P')).subtype ∘ₗ
    e.symm.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict
  let Yl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P)).subtype ∘ₗ
    e.toLinearMap ∘ₗ (Matrix.toLin' P').rangeRestrict
  refine ⟨LinearMap.toMatrix' Xl, LinearMap.toMatrix' Yl, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have hw := (e.symm ((Matrix.toLin' P).rangeRestrict v)).2
  have h1 : (Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ))) =
      e.symm ((Matrix.toLin' P).rangeRestrict v) := by
    apply Subtype.ext
    change Matrix.toLin' P' (Matrix.toLin' P' _) = _
    rw [hid' _ hw, hid' _ hw]
  change ((e ((Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ)))) :
      LinearMap.range (Matrix.toLin' P)) : Fin g → ℂ) = Matrix.toLin' P v
  rw [h1, LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.TraceEqualFinrank
end

section

namespace GlobalTheory

open Module

theorem relation_descends_along_functional (K A B : Type) [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B)
    (hrd : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f) (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ W) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (φ : ℂ →+ K) (hφ : ∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c)
    {ι : Type} [Fintype ι] (x : ι → A) (hx : ∀ s, x s ∈ W) (c : ι → ℂ)
    (h : ∑ s, c s • rd (x s) = 0) : ∑ s, φ (c s) • x s = 0 := by
  classical
  obtain ⟨n, ⟨bW⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K W) := ⟨_, ⟨Module.finBasis K W⟩⟩
  have hli : LinearIndependent K (fun j => (bW j : A)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli' := hW n (fun j => (bW j : A)) (fun j => (bW j).2) hli
  have hcoord : ∃ α : ι → Fin n → K, ∀ s, x s = ∑ j, α s j • (bW j : A) := by
    refine ⟨fun s j => bW.repr ⟨x s, hx s⟩ j, fun s => ?_⟩
    have h1 := congrArg (fun v : W => (v : A)) (bW.sum_repr ⟨x s, hx s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := hcoord
  have hrdx : ∀ s, rd (x s) = ∑ j, σ (α s j) • rd (bW j : A) := by
    intro s

    rw [hα s, map_sum]
    simp only [hrd]
  have hcoef : ∀ j, ∑ s, c s * σ (α s j) = 0 := by
    have h' : ∑ j, (∑ s, c s * σ (α s j)) • rd (bW j : A) = 0 := by
      rw [← h]
      simp only [hrdx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => Fintype.linearIndependent_iff.mp hli' _ h' j
  have hgoal : ∑ s, φ (c s) • x s = ∑ j, (∑ s, φ (c s) * α s j) • (bW j : A) := by
    simp only [hα, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hgoal]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h5 : ∑ s, φ (c s) * α s j = φ (∑ s, c s * σ (α s j)) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm (c s), hφ]
    exact mul_comm _ _
  rw [h5, hcoef j, map_zero, zero_smul]

theorem exists_functional_ne_zero_of_embedding (K : Type) [Field K] (σ : K →+* ℂ) (m : ℂ)
    (hm : m ≠ 0) : ∃ φ : ℂ →+ K, (∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c) ∧ φ m ≠ 0 := by
  let _ : Algebra K ℂ := σ.toAlgebra
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K ℂ, f m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hm ((Module.forall_dual_apply_eq_zero_iff K m).mp hcon)
  refine ⟨f.toAddMonoidHom, fun a c => ?_, hf⟩
  have hsmul : σ a * c = a • c := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  simp only [LinearMap.toAddMonoidHom_coe, hsmul, LinearMap.map_smul, smul_eq_mul]

theorem exists_rational_multiplier_of_complex :
    ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  classical
  intro K A B _ _ _ _ _ σ rd hrd V V' _ _ hVV h hspan hne
  have : FiniteDimensional K ↥(V * V') :=
    Module.Finite.iff_fg.mpr (Submodule.FG.mul (Module.Finite.iff_fg.mp inferInstance)
      (Module.Finite.iff_fg.mp inferInstance))
  have hrdsum : ∀ {m : ℕ} (a : Fin m → K) (v : Fin m → A),
      rd (∑ j, a j • v j) = ∑ j, σ (a j) • rd (v j) := by
    intro m a v

    rw [map_sum]
    simp only [hrd]
  have hexp : ∀ {U : Submodule K A} {m : ℕ} (b : Basis (Fin m) K U) (u : U),
      (u : A) = ∑ j, b.repr u j • (b j : A) := by
    intro U m b u
    have h1 := congrArg (fun v : U => (v : A)) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨n, ⟨bV⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V) := ⟨_, ⟨Module.finBasis K V⟩⟩
  obtain ⟨n', ⟨bV'⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K V') := ⟨_, ⟨Module.finBasis K V'⟩⟩
  have hC : ∀ i, ∃ C : Fin n' → ℂ, h * rd (bV i : A) = ∑ j, C j • rd (bV' j : A) := by
    intro i
    have hm := hspan _ (bV i).2
    have hsub : Submodule.span ℂ (rd '' (V' : Set A)) ≤
        Submodule.span ℂ (Set.range fun j => rd (bV' j : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have e : u = ∑ j, bV'.repr ⟨u, hu⟩ j • (bV' j : A) := hexp bV' ⟨u, hu⟩
      rw [e, hrdsum]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨C, hCe⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hsub hm)
    exact ⟨C, hCe.symm⟩
  choose C hC using hC
  have hi0 : ∃ i, h * rd (bV i : A) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨f, hf, hfne⟩ := hne
    apply hfne
    have e : f = ∑ j, bV.repr ⟨f, hf⟩ j • (bV j : A) := hexp bV ⟨f, hf⟩
    rw [e, hrdsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, hcon i, smul_zero]
  obtain ⟨i0, hi0⟩ := hi0
  have hj0 : ∃ j, C i0 j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hi0
    rw [hC i0]
    exact Finset.sum_eq_zero fun j _ => by rw [hcon j, zero_smul]
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨φ, hφ, hφne⟩ := exists_functional_ne_zero_of_embedding K σ (C i0 j0) hj0
  obtain ⟨T, hT⟩ : ∃ T : V →ₗ[K] V', ∀ i, T (bV i) = ∑ j, φ (C i j) • bV' j :=
    ⟨bV.constr K (fun i => ∑ j, φ (C i j) • bV' j), fun i => bV.constr_basis K _ i⟩
  have hTA : ∀ i, ((T (bV i) : V') : A) = ∑ j, φ (C i j) • (bV' j : A) := by
    intro i
    rw [hT]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hbasis : ∀ i k, ((T (bV i) : V') : A) * (bV k : A) = (bV i : A) * ((T (bV k) : V') : A) := by
    intro i k
    have key := relation_descends_along_functional K A B σ rd hrd (V * V') hVV φ hφ
      (ι := Fin n' ⊕ Fin n')
      (Sum.elim (fun j => (bV k : A) * (bV' j : A)) (fun j => (bV i : A) * (bV' j : A)))
      (by
        rintro (j | j)
        · exact Submodule.mul_mem_mul (bV k).2 (bV' j).2
        · exact Submodule.mul_mem_mul (bV i).2 (bV' j).2)
      (Sum.elim (fun j => C i j) (fun j => - C k j))
      (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, map_mul, neg_smul, Finset.sum_neg_distrib]
        simp only [← mul_smul_comm, ← Finset.mul_sum, ← hC]
        ring)
    rw [Fintype.sum_sum_type] at key
    simp only [Sum.elim_inl, Sum.elim_inr, map_neg, neg_smul, Finset.sum_neg_distrib,
      ← mul_smul_comm, ← Finset.mul_sum] at key
    rw [hTA, hTA, mul_comm _ ((bV k : V) : A)]
    rw [mul_neg] at key
    exact add_neg_eq_zero.mp key
  have hleft : ∀ i (g : V), ((T (bV i) : V') : A) * (g : A) = (bV i : A) * ((T g : V') : A) := by
    intro i g
    have h2 := bV.ext (f₁ := (LinearMap.mulLeft K ((T (bV i) : V') : A)).comp V.subtype)
      (f₂ := (LinearMap.mulLeft K ((bV i : V) : A)).comp (V'.subtype.comp T))
      (fun k => by simpa using hbasis i k)
    simpa using LinearMap.congr_fun h2 g
  refine ⟨T, ?_, fun f g => ?_⟩
  · intro hT0
    have h1 : T (bV i0) = 0 := by rw [hT0, LinearMap.zero_apply]
    rw [hT] at h1
    exact hφne (Fintype.linearIndependent_iff.mp bV'.linearIndependent _ h1 j0)
  · have h2 := bV.ext (f₁ := (LinearMap.mulRight K (g : A)).comp (V'.subtype.comp T))
      (f₂ := (LinearMap.mulRight K ((T g : V') : A)).comp V.subtype)
      (fun i => by simpa using hleft i g)
    simpa using LinearMap.congr_fun h2 f

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem ker_le_span_image_ker_of_semilinear :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by
  intro K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker θ)
  let b := Module.finBasis K C
  have hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have h1 : (m : X) ∈ LinearMap.ker θ := hm
    have h2 : (m : X) ∈ LinearMap.ker θ ⊓ C := ⟨h1, m.2⟩
    rw [hC.inf_eq_bot] at h2
    exact Subtype.ext (by simpa using h2)
  have hli : LinearIndependent K (fun k => θ (b k : X)) :=
    b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj
  have hli2 := hind _ _ hli
  set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN
  have hNT : N ≤ LinearMap.ker T := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : θ x = 0 := hx
    show T (j x) = 0
    rw [hT, hx', map_zero]
  have htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker θ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_
    have hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X) := by
      have := congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm

    rw [hcs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro h hh
  have hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) := by
    rw [htop]; trivial
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  have hTu : T u = 0 := hNT hu
  have h0 : ∑ k, a k • jW (θ (b k : X)) = 0 := by
    have : T (u + ∑ k, a k • j (b k : X)) = 0 := hh

    rw [map_add (f := _), hTu, zero_add, map_sum] at this
    simpa [hT] using this
  have ha := Fintype.linearIndependent_iff.1 hli2 a h0
  simpa [ha] using hu

end GlobalTheory
end

section

namespace GlobalTheory

theorem ringHom_extends_algHom_of_span_of_finrank_eq :
    ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A]
      [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B),
      Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O →
      ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  intro O _ _ _ A _ _ _ B _ _ φ ρ hspan hdim
  classical
  let b := Module.Free.chooseBasis ℤ O
  let v : Module.Free.ChooseBasisIndex ℤ O → A := fun i => φ (b i)
  have hle : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm

    rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℂ A := by
    rw [hdim, Module.finrank_eq_card_chooseBasisIndex]
  let bA := basisOfTopLeSpanOfCardEqFinrank v hle hcard
  have hbA : ∀ i, bA i = φ (b i) := fun i => by
    simp only [bA, coe_basisOfTopLeSpanOfCardEqFinrank, v]
  let L : A →ₗ[ℂ] B := bA.constr ℂ (fun i => ρ (b i))
  have hLb : ∀ i, L (φ (b i)) = ρ (b i) := by
    intro i
    rw [← hbA]
    exact bA.constr_basis ℂ _ i
  have hLφ : ∀ x, L (φ x) = ρ x := by
    have h : (L.restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap
        = ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => hLb i)
    intro x
    exact LinearMap.congr_fun h x
  have hmul : ∀ u w : A, L (u * w) = L u * L w := by
    have h : (LinearMap.mul ℂ A).compr₂ L = (LinearMap.mul ℂ B).compl₁₂ L L := by
      refine bA.ext (fun i => bA.ext (fun j => ?_))
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', hbA]
      rw [← map_mul, hLφ, hLφ, hLφ, map_mul]
    intro u w
    exact LinearMap.congr_fun₂ h u w
  have hone : L 1 = 1 := by
    rw [← map_one φ, hLφ, map_one]
  exact ⟨AlgHom.ofLinearMap L hone hmul, fun x => by
    simp only [AlgHom.ofLinearMap_apply]; exact hLφ x⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem commuting_map_eq_smul_multiplier :
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] (W W' : Submodule ℂ B) [FiniteDimensional ℂ W] (h h' : B), h * h' = 1 → (∀ w ∈ W', h' * w ∈ W) → ∀ T : W →ₗ[ℂ] W', T ≠ 0 → (∀ f g : W, (T f : B) * (g : B) = (f : B) * (T g : B)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : W, (T f : B) = a • (h * (f : B)) := by
  intro B _ _ _ W W' _ h h' hhh hW T hT hcomm
  let S : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩
      map_add' := fun f g => by ext; simp [mul_add]
      map_smul' := fun c f => by ext; simp [mul_smul_comm] }
  haveI : Nontrivial W := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT
    ext f
    rw [Subsingleton.elim f 0]
    simp
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue S
  obtain ⟨f₀, hf₀⟩ := ha.exists_hasEigenvector
  have hS : S f₀ = a • f₀ := hf₀.apply_eq_smul
  have h0 : (T f₀ : B) = a • (h * (f₀ : B)) := by
    have hc : h' * (T f₀ : B) = a • (f₀ : B) := by
      have := congrArg (fun x : W => (x : B)) hS
      simpa [S] using this
    calc (T f₀ : B) = h * (h' * T f₀) := by rw [← mul_assoc, hhh, one_mul]
    _ = h * (a • (f₀ : B)) := by rw [hc]
    _ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _
  have hf0ne : (f₀ : B) ≠ 0 := by
    intro hz
    exact hf₀.2 (Subtype.ext hz)
  have key : ∀ f : W, (T f : B) = a • (h * (f : B)) := by
    intro f
    have hx := hcomm f f₀
    rw [h0] at hx
    apply mul_right_cancel₀ hf0ne
    rw [hx]
    simp only [Algebra.smul_def]
    ring
  refine ⟨a, ?_, key⟩
  rintro rfl
  apply hT
  ext f
  simp [key f]

end GlobalTheory
end
