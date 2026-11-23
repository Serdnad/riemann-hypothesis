module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | exact GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | (intros; apply GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by

        simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _

  simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.SkewSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ (fun b => cc (y b)) := by
  unfold herm
  rw [Finset.sum_comm]
  simp [dotProduct, vecMul, Finset.sum_mul]

theorem herm_sum_left {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G ((∑ i, c i • v i) *ᵥ u) w = ∑ i, c i * herm G (v i *ᵥ u) w := by
  simp only [herm_eq_dot, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.sum_vecMul,
    Matrix.smul_vecMul, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem herm_sum_right {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E) (c : ι → E)
    (v : ι → Matrix (Fin r) (Fin r) E) (u w : Fin r → E) :
    herm G u ((∑ i, c i • v i) *ᵥ w) = ∑ i, cc (c i) * herm G u (v i *ᵥ w) := by
  have : (fun b => cc (((∑ i, c i • v i) *ᵥ w) b))
      = ∑ i, cc (c i) • (fun b => cc ((v i *ᵥ w) b)) := by
    funext b
    simp [cc, Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply]
  simp only [herm_eq_dot, this, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem eq_zero_of_herm (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (Y : Matrix (Fin r) (Fin r) E) (h : ∀ u w, herm G (Y *ᵥ u) w = 0) : Y = 0 := by
  have key : ∀ u, Y *ᵥ u = 0 := by
    intro u
    apply Matrix.eq_zero_of_vecMul_eq_zero hG
    funext b
    have := h u (Pi.single b 1)
    rw [herm_eq_dot] at this
    have h2 : (fun b' => cc ((Pi.single b (1 : E) : Fin r → E) b')) = Pi.single b 1 := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [cc]
      · simp [cc, hb]
    rw [h2] at this
    simpa using this
  ext a b
  have := congrFun (key (Pi.single b 1)) a
  simpa using this

theorem linearIndependent_of_skew {ι : Type} [Fintype ι] (G : Matrix (Fin r) (Fin r) E)
    (hG : G.det ≠ 0) (v : ι → Matrix (Fin r) (Fin r) E)
    (hv : ∀ i u w, herm G (v i *ᵥ u) w + herm G u (v i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) v) : LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  have step : ∀ c : ι → E, ∑ i, c i • v i = 0 → ∀ i, c i + cc (c i) = 0 := by
    intro c hc
    have h1 : ∑ i, cc (c i) • v i = 0 := by
      apply eq_zero_of_herm G hG
      intro u w
      have h := herm_sum_right G c v u w
      rw [hc] at h
      have h0 : herm G u ((0 : Matrix (Fin r) (Fin r) E) *ᵥ w) = 0 := by simp [herm, cc]
      rw [h0] at h
      rw [herm_sum_left, ← neg_eq_zero, ← Finset.sum_neg_distrib, h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eq_neg_of_add_eq_zero_right (hv i u w)]; ring
    have hm : ∀ i, c i + cc (c i) ∈ maximalRealSubfield E := by
      intro i
      rw [← IsCMField.complexConj_eq_self_iff]
      simp [cc, add_comm]
    intro i
    have := hli (fun i => ⟨c i + cc (c i), hm i⟩) (by
      have : ∑ i, (c i + cc (c i)) • v i = 0 := by
        simp only [add_smul, Finset.sum_add_distrib, hc, h1, add_zero]
      exact this) i
    exact congrArg Subtype.val this
  intro c hc j
  have h := step (fun i => cc (c j) * c i) (by
    simp only [mul_smul, ← Finset.smul_sum, hc, smul_zero]) j
  have h2 : 2 * (cc (c j) * c j) = 0 := by
    rw [← h]; simp [cc]; ring
  simp [cc] at h2
  exact h2

theorem finrank_ker_trace (K : Type) [Field K] (r : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) K K)) = (r + 1) ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin (r + 1)) K K)
  have hs : LinearMap.range (Matrix.traceLinearMap (Fin (r + 1)) K K) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨Matrix.single 0 0 a, by simp⟩
  rw [hs, finrank_top, Module.finrank_self, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  rw [sq]; omega

theorem mem_span_of_skew : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → ∀ X : Matrix (Fin r) (Fin r) E, X.trace = 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → X ∈ Submodule.span (maximalRealSubfield E) (Set.range e) := by
  intro E _ _ _ r G e _ hG he hli X hX hXs
  rcases r with _ | r
  · have : X = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  by_contra hn
  have h1 : LinearIndependent (maximalRealSubfield E) (fun o : Option _ => Option.casesOn' o X e) :=
    hli.option hn
  have h2 := linearIndependent_of_skew G hG _ (by
    rintro (_ | i)
    · exact hXs
    · exact (he i).2) h1
  let f : Option (Fin ((r + 1) ^ 2 - 1)) →
      LinearMap.ker (Matrix.traceLinearMap (Fin (r + 1)) E E) := fun o =>
    ⟨Option.casesOn' o X e, by
      rcases o with _ | i
      · exact hX
      · exact (he i).1⟩
  have h3 : LinearIndependent E f := LinearIndependent.of_comp (Submodule.subtype _) h2
  have h4 := h3.fintype_card_le_finrank
  rw [finrank_ker_trace] at h4
  simp at h4

end GlobalTheory.SkewSpan
end

section

open NumberField Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem suLie_finrank_ge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, (e i).trace = 0 ∧ ∀ x y, herm G (e i *ᵥ x) y + herm G x (e i *ᵥ y) = 0) ∧
      LinearIndependent (maximalRealSubfield E) e := by
  intro E _ _ _ r G hG hdet
  let F := maximalRealSubfield E
  have cc_mul : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have cc_F : ∀ (c : F) (x : E), cc (c • x) = c • cc x := by
    intro c x
    have hc : cc (c : E) = c := (IsCMField.complexConj_eq_self_iff E _).mpr c.2
    show cc ((c : E) * x) = (c : E) * cc x
    rw [cc_mul, hc]
  have hs : ∀ (f : Fin r → E), cc (∑ i, f i) = ∑ i, cc (f i) := fun f => map_sum (IsCMField.complexConj E) f _
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  have hV : Module.finrank F (Matrix (Fin r) (Fin r) E) = r * r * 2 := by
    rw [Module.finrank_matrix, Algebra.IsQuadraticExtension.finrank_eq_two F E]; simp

  let conjL : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => X.map cc
      map_add' := fun X Y => by ext a b; simp [cc_add]
      map_smul' := fun c X => by ext a b; simp [cc_F] }
  let φ : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun X => Xᵀ * G + G * conjL X
      map_add' := fun X Y => by simp only [map_add (f := _), transpose_add, Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' := fun c X => by
        simp only [map_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, smul_add] }

  let H : Submodule F (Matrix (Fin r) (Fin r) E) :=
    { carrier := {M | ∀ a b, cc (M a b) = M b a}
      add_mem' := fun {M N} hM hN a b => by simp [cc_add, hM a b, hN a b]
      zero_mem' := fun a b => by simp [cc]
      smul_mem' := fun c M hM a b => by simp [cc_F, hM a b] }
  have hφH : LinearMap.range φ ≤ H := by
    rintro _ ⟨X, rfl⟩ a b
    have hφX : φ X = Xᵀ * G + G * X.map cc := rfl
    show cc ((φ X) a b) = (φ X) b a
    rw [hφX]
    simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, map_apply, cc_add]
    rw [hs, hs, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> simp only [cc_mul, cc_cc, hG] <;> ring

  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hy' : cc y ≠ y := hy
  set δ : E := y - cc y with hδdef
  have hδ : cc δ = -δ := by rw [hδdef, show cc (y - cc y) = cc y - cc (cc y) from map_sub _ _ _, cc_cc]; ring
  have hδ0 : δ ≠ 0 := fun h => hy' (sub_eq_zero.mp h).symm
  let Dm : Matrix (Fin r) (Fin r) E →ₗ[F] Matrix (Fin r) (Fin r) E :=
    { toFun := fun M => δ • M
      map_add' := fun M N => smul_add δ M N
      map_smul' := fun c M => smul_comm δ c M }
  have hDm : Function.Injective Dm := fun M N h => smul_right_injective _ hδ0 h
  have hinf : H ⊓ H.map Dm = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro M ⟨hM, N, hN, rfl⟩
    have hN0 : ∀ a b, N a b = 0 := by
      intro a b
      have h := hM b a
      change cc (δ * N b a) = δ * N a b at h
      rw [cc_mul, hδ, hN b a] at h
      have : δ * N a b = 0 := by linear_combination (-1/2 : E) * h
      exact (mul_eq_zero.mp this).resolve_left hδ0
    ext a b
    show δ * N a b = 0
    rw [hN0, mul_zero]
  have hHmap : Module.finrank F (H.map Dm) = Module.finrank F H :=
    (Submodule.equivMapOfInjective Dm hDm H).finrank_eq.symm
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_mono hφH
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq H (H.map Dm)
  have h4 := Submodule.finrank_le (H ⊔ H.map Dm)
  rw [hinf, finrank_bot] at h3
  have hK : r * r ≤ Module.finrank F (LinearMap.ker φ) := by omega

  let t : Matrix (Fin r) (Fin r) E →ₗ[F] E := Matrix.traceLinearMap (Fin r) F E
  let f := t.domRestrict (LinearMap.ker φ)
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hf : LinearMap.range f ≤ Submodule.span F {δ} := by
    rintro _ ⟨⟨X, hX⟩, rfl⟩
    have hX' : Xᵀ * G + G * X.map cc = 0 := hX
    have hbar : X.map cc = -(G⁻¹ * (Xᵀ * G)) := by
      have : G * X.map cc = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right hX'
      calc X.map cc = G⁻¹ * (G * X.map cc) := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
        _ = -(G⁻¹ * (Xᵀ * G)) := by rw [this, Matrix.mul_neg]
    have htr : cc X.trace = -X.trace := by
      have e1 : (X.map cc).trace = cc X.trace := by
        simp only [Matrix.trace, Matrix.diag, map_apply]; exact (hs _).symm
      rw [← e1, hbar, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv G hu, Matrix.mul_one, Matrix.trace_transpose]
    have hz : cc (X.trace / δ) = X.trace / δ := by
      rw [show cc (X.trace / δ) = cc X.trace / cc δ from map_div₀ (IsCMField.complexConj E) _ _, htr, hδ,
        neg_div_neg_eq]
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨X.trace / δ, (IsCMField.complexConj_eq_self_iff E _).mp hz⟩, ?_⟩
    show X.trace / δ * δ = X.trace
    exact div_mul_cancel₀ _ hδ0

  have hv : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ fun b => cc (v b)) := by
    intro u v
    simp only [herm, dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hcv : ∀ (X : Matrix (Fin r) (Fin r) E) (y : Fin r → E),
      (fun b => cc ((X *ᵥ y) b)) = X.map cc *ᵥ fun b => cc (y b) := by
    intro X y; ext b
    simp only [mulVec, dotProduct, map_apply]
    exact (hs _).trans (Finset.sum_congr rfl fun c _ => cc_mul _ _)
  have skew : ∀ X : Matrix (Fin r) (Fin r) E, Xᵀ * G + G * X.map cc = 0 →
      ∀ x y, herm G (X *ᵥ x) y + herm G x (X *ᵥ y) = 0 := by
    intro X hX x y
    rw [hv, hv, hcv, ← vecMul_transpose X x, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
      ← dotProduct_add, ← add_mulVec, hX, zero_mulVec, dotProduct_zero]

  have h5 := LinearMap.finrank_range_add_finrank_ker f
  have h6 := (Submodule.finrank_mono hf).trans (finrank_span_singleton hδ0).le
  have hle : r ^ 2 - 1 ≤ Module.finrank F (LinearMap.ker f) := by rw [sq]; omega
  let b := Module.finBasis F (LinearMap.ker f)
  let g : LinearMap.ker f →ₗ[F] Matrix (Fin r) (Fin r) E :=
    (LinearMap.ker φ).subtype ∘ₗ (LinearMap.ker f).subtype
  have hg : LinearMap.ker g = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp Subtype.val_injective)
  refine ⟨fun i => g (b (Fin.castLE hle i)), fun i => ?_,
    (b.linearIndependent.comp _ (Fin.castLE_injective hle)).map' g hg⟩
  have hx1 : f (b (Fin.castLE hle i)).1 = 0 := (b (Fin.castLE hle i)).2
  have hx2 : φ (b (Fin.castLE hle i)).1.1 = 0 := (b (Fin.castLE hle i)).1.2
  exact ⟨hx1, skew _ hx2⟩

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem lattice_mod_reps_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E),
    T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  intro E _ _ _ r M Λ hM hfg
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  have hLfg : L.FG := hfg.restrictScalars
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hLfg
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b := Module.Free.chooseBasis ℤ L
  have hli : LinearIndependent ℤ (fun i => (b i : Fin r → E)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliQ : LinearIndependent ℚ (fun i => (b i : Fin r → E)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
  have hcard : Fintype.card ι ≤ Module.finrank ℚ (Fin r → E) := hliQ.fintype_card_le_finrank
  have hfr : Module.finrank ℚ (Fin r → E) = r * Module.finrank ℚ E := by
    simp [Module.finrank_pi_fintype]
  have heven : Module.finrank ℚ E = 2 * fdeg E := by
    rw [fdeg, IsTotallyComplex.finrank E]; omega
  have hn : Fintype.card ι ≤ 2 * fdeg E * r := by
    rw [hfr, heven] at hcard; linarith [Nat.mul_comm r (2 * fdeg E)]
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  let f : (ι → Fin M) → (Fin r → E) := fun c => ((∑ i, ((c i : ℕ) : ℤ) • b i : L) : Fin r → E)
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (ι → Fin M)).card :=
          Finset.card_image_le
      _ = M ^ Fintype.card ι := by simp
      _ ≤ M ^ (2 * fdeg E * r) := Nat.pow_le_pow_right hM hn
  · intro t ht
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ht
    exact (∑ i, ((c i : ℕ) : ℤ) • b i : L).2
  · intro x hx
    let xl : L := ⟨x, hx⟩
    let k := b.repr xl
    let c : ι → Fin M := fun i => ⟨(k i % M).toNat, by
      have := Int.emod_nonneg (k i) hMpos.ne'
      have := Int.emod_lt_of_pos (k i) hMpos
      omega⟩
    refine ⟨f c, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ((∑ i, (k i / M) • b i : L) : Fin r → E), (∑ i, (k i / M) • b i : L).2, ?_⟩
    have hsum : xl = ∑ i, ((c i : ℕ) : ℤ) • b i + (M : ℤ) • ∑ i, (k i / M) • b i := by
      conv_lhs => rw [← b.sum_repr xl]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      show k i = ((k i % M).toNat : ℤ) + M * (k i / M)
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hMpos.ne')]
      linarith [Int.mul_ediv_add_emod (k i) (M : ℤ)]
    have h2 := congrArg Subtype.val hsum
    calc x = (xl : Fin r → E) := rfl
      _ = _ := h2
      _ = f c + M • ((∑ i, (k i / M) • b i : L) : Fin r → E) := by
        rw [Submodule.coe_add, Submodule.coe_smul, natCast_zsmul]

end GlobalTheory
end
