module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.MeanValue
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open TopologicalSpace TensorProduct

namespace GlobalTheory.AnPer

theorem Step.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (s : Step J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Step J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  obtain ⟨n, h1, h2, h3⟩ := s
  refine ⟨fun a ↦ (1 : D) ⊗ₜ[ℂ] n a, fun a ↦ hJ _ (h1 a), fun a b ↦ by simp [h2], fun f ↦ ?_⟩
  have key : ∀ x : D ⊗[ℂ] Hol W₀, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ x +
        ∑ a, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ (LinearMap.lTensor D (dw (W := W₀) a).toLinearMap x) *
          (1 : D) ⊗ₜ[ℂ] n a := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul d h =>
      have := h3 h
      simp only [RingHom.coe_coe] at this
      simp [this, tmul_add, tmul_sum]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy, add_mul, Finset.sum_add_distrib]
      abel
  simpa [hT] using key (Ta f)

theorem Close.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (h : Close J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  have key : ∀ ρ : Hol W₀ →+* C, Close J (ρ₁ : Hol W₀ →+* C) ρ → ∃ σ : Hol W₀ →ₐ[ℂ] C, (σ : Hol W₀ →+* C) = ρ ∧
      Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id ℂ D) σ).comp Ta).toRingHom := by
    intro ρ hρ
    induction hρ with
    | refl => exact ⟨ρ₁, rfl, Relation.ReflTransGen.refl⟩
    | @tail b c _ s ih =>
      obtain ⟨σ, rfl, ih⟩ := ih
      have hc : ∀ z : ℂ, c (algebraMap ℂ (Hol W₀) z) = algebraMap ℂ C z := by
        intro z
        obtain ⟨n, -, -, h3⟩ := s
        rw [h3]
        simp [Derivation.map_algebraMap]
      exact ⟨{ c with commutes' := hc }, rfl,
        Relation.ReflTransGen.tail ih (Step.tensor_comp Ta hT J J' hJ σ { c with commutes' := hc } s)⟩
  obtain ⟨σ, hσ, h'⟩ := key _ h
  obtain rfl : σ = ρ₂ := AlgHom.toRingHom_injective hσ
  exact h'

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

theorem exists_glue_fn {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (hK : K.Rich) (a : ∀ k, Hol (K.W k)) (ha : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') :
    ∃ G : Tot I g → ℂ, ∀ k, ∀ q ∈ K.W k, G q = (a k).fn q := by
  classical
  have key : ∀ k₁ k₂ q, q ∈ K.W k₁ → q ∈ K.W k₂ → (a k₁).fn q = (a k₂).fn q := by
    intro k₁ k₂ q h₁ h₂
    obtain ⟨k, hk, e₁, e₂⟩ := hK.2 0 k₁ k₂ q h₁ (by rw [F.shift_zero]; exact h₂)
    have r₁ := fn_sh e₁ (a k₁) hk
    have r₂ := fn_sh e₂ (a k₂) hk
    rw [ha, F.shift_zero] at r₁ r₂
    rw [← r₁, ← r₂]
  refine ⟨fun q ↦ if h : ∃ k, q ∈ K.W k then (a h.choose).fn q else 0, fun k q hq ↦ ?_⟩
  have h : ∃ k, q ∈ K.W k := ⟨k, hq⟩
  simp only [dif_pos h]
  exact key _ _ q h.choose_spec hq

theorem exists_cst_of_dw_eq_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k') →
    (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  intro I _ g Λ _ F K hK a ha hd
  obtain ⟨G, hG⟩ := exists_glue_fn K hK a ha
  have ev : ∀ k, ∀ q ∈ K.W k, G =ᶠ[𝓝 q] (a k).fn := fun k q hq ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hq] with r hr using hG k r hr
  have an : ∀ q : Tot I g, q.1 ∈ F.V → AnalyticAt ℂ G q := fun q hq ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    exact ((a k).analytic q hk).congr (ev k q hk).symm
  have d0 : ∀ q : Tot I g, q.1 ∈ F.V → ∀ i, fderiv ℂ G q ((0, Pi.single i 1) : Tot I g) = 0 := fun q hq i ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    rw [(ev k q hk).fderiv_eq, ← Hol.fn_der _ _ hk]
    change (dw i (a k)).fn q = 0
    rw [hd, ← Hol.ev_apply q hk, map_zero]
  have cs : ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0) := fun z hz w ↦ by
    have hf : ∀ w : Fin g → ℂ, HasFDerivAt (fun w ↦ G (z, w))
        ((fderiv ℂ G (z, w)).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ))) w := fun w ↦
      (an (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)
    refine is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun w ↦ G (z, w)) (fun w ↦ (hf w).differentiableAt)
      (fun w ↦ ?_) w 0
    rw [(hf w).fderiv]
    ext v
    have hv : ((0, v) : Tot I g) = ∑ i, v i • ((0, Pi.single i 1) : Tot I g) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    change fderiv ℂ G (z, w) (0, v) = 0

    rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, d0 (z, w) hz i, smul_zero]
  refine ⟨Hol.mk (fun z ↦ G (z, 0)) fun z hz ↦
    AnalyticAt.comp (g := G) (f := fun z ↦ ((z, 0) : Tot I g)) (an (z, 0) hz)
      (analyticAt_id.prod analyticAt_const), fun k ↦ Hol.ext_fn fun q hq ↦ ?_⟩
  rw [fn_cst _ _ _ hq, ← hG k q hq]
  exact (cs q.1 (K.base k q hq) q.2).trans (Hol.fn_mk (fun z ↦ G (z, 0)) _ (K.base k q hq)).symm

end GlobalTheory.AnPer.Charts
end

section

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_composable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (l m : Λ) (q : Tot I g) (hq : q.1 ∈ F.V) :
    ∃ k k' k'' : K.K, K.le l k' k ∧ K.le m k'' k' ∧ q ∈ K.W k'' := by
  obtain ⟨hcov, hjoin⟩ := hK
  obtain ⟨k, hk⟩ := hcov (F.shift l (F.shift m q)) hq
  obtain ⟨k₁, hk₁⟩ := hcov (F.shift m q) hq
  obtain ⟨k', hk', -, hlk⟩ := hjoin l k₁ k (F.shift m q) hk₁ hk
  obtain ⟨k₂, hk₂⟩ := hcov q hq
  obtain ⟨k'', hk'', -, hmk⟩ := hjoin m k₂ k' q hk₂ hk'
  exact ⟨k, k', k'', hlk, hmk, hk''⟩

theorem eq_zero_of_cst_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V),
    (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  intro I _ g Λ _ F K hK l m p hp
  apply Hol.ext_fn
  intro z hz
  obtain ⟨k, k', k'', h1, h2, hq⟩ := exists_composable K hK l m ((z, 0) : Tot I g) hz
  have h : (K.cst k'' p).fn ((z, 0) : Tot I g) = (0 : Hol (K.W k'')).fn ((z, 0) : Tot I g) := by
    rw [hp k k' k'' h1 h2]
  rw [fn_cst K k'' p hq, show (0 : Hol (K.W k'')) = algebraMap ℂ _ 0 from (map_zero _).symm,
    Hol.fn_algebraMap _ hq] at h
  rw [show (0 : Hol F.V) = algebraMap ℂ _ 0 from (map_zero _).symm, Hol.fn_algebraMap _ hz]
  exact h

end GlobalTheory.AnPer.Charts
end

section

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem exists_shift_retraction (H : ∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') (l : Λ) (T : K.Obj) :
    ∃ (S : K.Obj) (s : S ⟶ T) (s' : T ⟶ S), s.deg = l ∧ s'.deg = -l ∧ s' ≫ s = 𝟙 T := by
  obtain ⟨k, h1, h2⟩ := H l T.k
  let S : K.Obj :=
    { k := k, C := T.C, J := T.J, nil := T.nil, ρ := T.ρ.comp (K.sh h1)
      ρ_cst := fun f ↦ (congrArg T.ρ (K.sh_cst h1 f)).trans (T.ρ_cst f) }
  have key : ∀ m (h : K.le m T.k T.k), m = 0 → ∀ f, K.sh h f = f := by
    rintro m h rfl f
    exact K.sh_refl h f
  have e : (T.ρ.comp (K.sh h1)).comp (K.sh h2) = T.ρ := RingHom.ext fun f ↦
    congrArg T.ρ ((K.sh_sh h2 h1 (K.le_trans h2 h1) f).trans (key _ _ (neg_add_cancel l) f))
  let s : S ⟶ T := ⟨AlgHom.id _ _, l, h1, fun _ h ↦ h, Relation.ReflTransGen.refl⟩
  let s' : T ⟶ S := ⟨AlgHom.id _ _, -l, h2, fun _ h ↦ h, by
    change Close T.J ((T.ρ.comp (K.sh h1)).comp (K.sh h2)) T.ρ
    rw [e]
    exact Relation.ReflTransGen.refl⟩
  exact ⟨S, s, s', rfl, rfl, hom_ext (fun _ ↦ rfl) (neg_add_cancel l)⟩

theorem eq_of_cst_eq (hR : K.Rich) {f f' : Hol F.V} (h : ∀ k, K.cst k f = K.cst k f') : f = f' :=
  Hol.ext_fn fun z hz ↦ by
    obtain ⟨k, hk⟩ := hR.1 (z, 0) hz
    exact (K.fn_cst k f hk).symm.trans ((congrArg (fun u ↦ Hol.fn u (z, 0)) (h k)).trans (K.fn_cst k f' hk))

end GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem const_biadditive_coboundary_symm : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ γ : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = d0 K.Oc γ T T' φ) → (∀ γ : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → mp K.Oc φ (γ T) = γ T') → ∃ r : Hol F.V, ∀ T, γ T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l := by
  intro I _ g Λ _ F K H1 H2 H3 hR β c hd l m
  obtain ⟨γ, hγ⟩ := H1 c fun T T' T'' φ ψ h h' ↦ by
    have := hd T T' T'' φ ψ
    rw [d1_apply, h', map_zero, map_zero] at this
    linear_combination -this
  obtain ⟨c', hc0, hd'⟩ : ∃ c' : C1 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c' T T' φ = 0) ∧
      ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), mp K.Oc ψ (c' T T' φ) - c' T T'' (φ ≫ ψ) + c' T' T'' ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg) := by
    refine ⟨fun T T' φ ↦ c T T' φ - d0 K.Oc γ T T' φ, fun T T' φ h ↦ sub_eq_zero.2 (hγ T T' φ h),
      fun T T' T'' φ ψ ↦ ?_⟩
    have e1 := hd T T' T'' φ ψ
    have e2 : d0 K.Oc γ T T'' (φ ≫ ψ) = mp K.Oc ψ (d0 K.Oc γ T T' φ) + d0 K.Oc γ T' T'' ψ := commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc γ φ ψ
    rw [d1_apply] at e1
    rw [map_sub]
    linear_combination e1 + e2
  choose S s s' hs hs' hss using Charts.exists_shift_retraction H3
  have hκ : ∀ (n : Λ) (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = n → c' T T' φ = c' _ T' (s n T') := by
    intro n T T' φ h
    have h0 : Charts.Hom.deg (φ ≫ s' n T') = 0 := by rw [Charts.comp_deg, h, hs', add_neg_cancel]
    have := hd' _ _ _ (φ ≫ s' n T') (s n T')
    rw [hc0 _ _ _ h0, h0, Category.assoc, hss, Category.comp_id, map_zero, map_zero, AddMonoidHom.zero_apply,
      map_zero] at this
    linear_combination -this
  have hr : ∀ n : Λ, ∃ r : Hol F.V, ∀ T, c' _ T (s n T) = algebraMap (Hol F.V) (K.Oc.obj T) r := fun n ↦
    H2 (fun T ↦ c' _ T (s n T)) fun T T' φ h ↦ by
      have := hd' _ _ _ (s n T) φ
      rw [hc0 _ _ _ h, h, map_zero, map_zero,
        hκ n _ _ (s n T ≫ φ) (by rw [Charts.comp_deg, h, hs, add_zero])] at this
      linear_combination this
  choose r hr using hr
  have main : ∀ (a b : Λ) (T : K.Obj), algebraMap (Hol F.V) (K.Oc.obj T) (β a b) =
      algebraMap (Hol F.V) (K.Oc.obj T) (r a - r (a + b) + r b) := by
    intro a b T
    have := hd' _ _ _ (s a (S b T)) (s b T)
    rw [hκ (a + b) _ _ (s a (S b T) ≫ s b T) (by rw [Charts.comp_deg, hs, hs]), hr, hr, hr, hs, hs,
      AlgHom.commutes] at this
    set_option synthInstance.maxHeartbeats 200000 in
      rw [← this, map_add (algebraMap (Hol F.V) (K.Oc.obj T)), map_sub]
  refine Charts.eq_of_cst_eq hR fun k ↦ ?_
  refine (main l m (K.triv k)).trans (Eq.trans ?_ (main m l (K.triv k)).symm)
  congr 1
  rw [add_comm m l]
  ring

end GlobalTheory.AnPer
end
end

section

set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
end

section

open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)

    rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
end

section

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

section Two

variable {m l m' l' : Type*}

variable [Fintype m] [Fintype l] [Fintype m'] [Fintype l']

variable [DecidableEq m] [DecidableEq l] {H₁ : E → Matrix m m ℂ} {H₂ : E → Matrix l l ℂ} {z : E}

end Two

section Family

variable {o : Type*} [DecidableEq o] {m m' : o → Type*}

theorem mdel_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun i => A i x) z ξ = blockDiagonal' fun i => mdel (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

theorem mdbar_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun i => A i x) z ξ =
      blockDiagonal' fun i => mdbar (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]


variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]


variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem isUnit_det_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by
  refine isUnit_det_of_right_inverse (B := blockDiagonal' fun i => (A i)⁻¹) ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext i
  exact mul_nonsing_inv _ (h i)

theorem conn_blockDiagonal' (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by
  refine (eq_conn_of_compatible (H := fun x => blockDiagonal' fun i => H i x)
    (isUnit_det_blockDiagonal' h) ?_).symm
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, ← blockDiagonal'_mul]
  congr 1
  funext i
  exact conn_transpose_mul (h i) ξ

theorem curv_blockDiagonal' {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun i => H i x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun i => conn (H i) x ξ :=
    (eventually_all.2 fun i => (d i).eventually_isUnit (h i)).mono
      fun x hx => conn_blockDiagonal' hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' fun i x => conn (H i) x ξ, ← blockDiagonal'_neg]
  rfl


end Family

end GlobalTheory.HermFrame
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isField_aic_sh : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  intro T _ hF hA
  letI : Field T := hF.toField
  refine ⟨Field.henselian T, ?_⟩
  haveI hT : IsAlgClosed T := by
    refine IsAlgClosed.of_exists_root T ?_
    intro p hm hirr
    obtain ⟨a, ha⟩ := hA p hm (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr))
    exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩
  have hinj : Function.Injective (IsLocalRing.residue T) := (IsLocalRing.residue T).injective
  have hbij : Function.Bijective (IsLocalRing.residue T) := ⟨hinj, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField T) :=
    IsAlgClosed.of_ringEquiv T _ (RingEquiv.ofBijective _ hbij)
  infer_instance

end GlobalTheory.EtC
end
