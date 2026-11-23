module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
open scoped ComplexOrder

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem stdZ_perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) := AddMonoidHom.mk' C.vec fun a b => by
    funext τ i
    simp [LatEmb.vec]
  have h : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    have e : C.vec (C.lam k) = C.bas k := by
      funext τ i
      exact (C.bas_eq k τ i).symm
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [e, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

theorem stdZ_sgU (τ : Ψ) {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : Aᴴ * C.sgr τ * A = sgI j j')
    (hA' : A'ᴴ * C.sgr τ * A' = sgI j j') : IsSgU (C.cinv A τ * A') := by
  have h1 := (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ A hA).2.1
  have e : A' = A * (C.cinv A τ * A') := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold IsSgU
  generalize C.cinv A τ * A' = v at e ⊢
  rw [e] at hA'
  refine Eq.trans ?_ hA'
  rw [← hA]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem stdZ_eqvBy_symm {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

omit [Fintype Ψ] in
theorem stdZ_zero_mem (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem stdZ_reach (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') :
    ∃ t ∈ ballDom F.q, C.IsAdapted (F.R t) A := by
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  have f1 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA τ)
  obtain ⟨R', h1, h2, -, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (fun τ => A τ * C.cinv (A0 τ) τ)
    (fun τ => A0 τ * C.cinv (A τ) τ) (F.form_eq 0) (fun τ => by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.cinv (A0 τ) τ), (f0 τ).1, Matrix.one_mul, (f1 τ).2.1])
    (fun τ => (f0 τ).2.2.2.2.2 _ (hA τ))
  have h5 := h4 A0 hA0
  have e : (fun τ => A τ * C.cinv (A0 τ) τ * A0 τ) = A := by
    funext τ
    rw [Matrix.mul_assoc, (f0 τ).1, Matrix.mul_one]
  rw [e] at h5
  have hs : R'.HasSig F.σ j j' := by
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [h2]
    exact this
  obtain ⟨t, ht, he⟩ := (F.univ R' (h1.trans (F.form_eq 0)) hs).exists
  exact ⟨t, ht, GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t) A h5 (stdZ_eqvBy_symm he)⟩

end

theorem stdZ : StdZ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨Z, G, hZ, hG, hZeq, hpot⟩ := GlobalTheory.T.holomorphic_adapted_frame_on_ball E Ψ j j' n g Λ F C A0 hA0
  have had : ∀ t ∈ ballDom F.q, ∃ A, C.IsAdapted (F.R t) A := fun t ht =>
    GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
  have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
    intro t ht
    obtain ⟨A, hA⟩ := had t ht
    rw [hZeq t ht A hA]
    exact (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q _ fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)).2.1 h0
  have hinj : Set.InjOn Z (ballDom F.q) := by
    intro t ht t' ht' h
    obtain ⟨A, hA⟩ := had t ht
    obtain ⟨A', hA'⟩ := had t' ht'
    rw [hZeq t ht A hA, hZeq t' ht' A' hA'] at h
    have e : (fun τ => C.cinv (A0 τ) τ * A' τ) = fun τ => (C.cinv (A0 τ) τ * A τ) * (C.cinv (A τ) τ * A' τ) := by
      funext τ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A τ), (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA.unit τ)).2.1,
        Matrix.one_mul]
    rw [e] at h
    have h1 := (GlobalTheory.T.ball_mobius_zero_eq_iff_unitary Ψ j j' n F.q _ _ (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ))
      (fun τ => stdZ_sgU C τ (hA.unit τ) (hA'.unit τ))).1 h
    have h2 := (GlobalTheory.T.adapted_frame_change_unitary E Ψ j j' n g Λ F C (F.R t) A A' (F.form_eq t) hA hA'.unit).2 h1
    have h3 := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (F.R t') A' (F.form_eq t) (F.form_eq t') h2 hA'
    exact (F.univ (F.R t') (F.form_eq _) (F.sig _ ht')).unique ⟨ht, h3⟩ ⟨ht', LinearEquiv.refl _ _, fun _ => rfl⟩
  have hsurj : Set.SurjOn Z (ballDom F.q) (ballDom F.q) := by
    intro s hs
    obtain ⟨w, hw, hws⟩ := GlobalTheory.T.ball_mobius_transitive Ψ j j' n F.q s hs
    obtain ⟨t, ht, hA⟩ := stdZ_reach C (fun τ => A0 τ * w τ) fun τ => by
      have hw' := hw τ
      unfold IsSgU at hw'
      rw [← hw']
      conv_rhs => rw [← hA0.unit τ]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨t, ht, ?_⟩
    rw [hZeq t ht _ hA, ← hws]
    congr 1
    funext τ
    rw [← Matrix.mul_assoc, (f0 τ).1, Matrix.one_mul]
  refine ⟨A0, hA0.unit, Z, ⟨hmaps, hinj, hsurj⟩, fun S hS hSD => ⟨?_, ?_⟩, ?_⟩
  · exact hS.image_of_continuousOn_injOn (hZ.continuousOn.mono hSD) (hinj.mono hSD)
  · exact ballMeas_image F.q hZ (fun t ht => hmaps ht) hinj
      (fun t ht => ballDens_transform F.q hZ hG (fun t ht => hmaps ht) hpot ht) hS hSD
  intro γ δ hδ _ hu t ht t' ht'
  obtain ⟨A, hA⟩ := had t ht
  let a : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  let ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    ((γ⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  have hai : ∀ τ, a τ * ai τ = 1 := fun τ => by
    simp only [a, ai]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hia : ∀ τ, ai τ * a τ = 1 := fun τ => mul_eq_one_comm.1 (hai τ)
  obtain ⟨R', h1, -, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R t) a ai (F.form_eq t) hai hu
  have h5 := h4 A hA
  have hP : ∀ x, R'.P (δ x) = (F.R t).P x := fun x => by
    rw [h3, ← stdZ_perExt_vec C (F.R t) x]
    congr 1
    funext τ
    have hv : C.vec (δ x) τ = a τ *ᵥ C.vec x τ := by
      funext i
      show embOf (F.σ τ) (C.e (δ x) i) = _
      rw [hδ]
      exact RingHom.map_mulVec _ _ _ i
    rw [hv, Matrix.mulVec_mulVec, hia, Matrix.one_mulVec]
  have hm : moebBall F.q (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ) (Z t) =
      moebBall F.q (fun τ => C.cinv (A0 τ) τ * (a τ * A τ)) 0 := by
    have hU : ∀ τ, IsSgU (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ τ) := fun τ =>
      ((f0 τ).2.2.2.2.1 _ _ (hai τ) (hu τ)).2.2.1
    rw [hZeq t ht A hA, ← GlobalTheory.T.ball_mobius_mul Ψ j j' n F.q _ _ hU (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)) 0 h0]
    congr 1
    funext τ
    show C.cinv (A0 τ) τ * (a τ * A0 τ) * (C.cinv (A0 τ) τ * A τ) = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A0 τ), (f0 τ).2.1, Matrix.one_mul]
  rw [hm]
  constructor
  · rintro ⟨k, hk⟩
    refine hZeq t' ht' _ (GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t') _ h5 ⟨k, fun x => ?_⟩)
    obtain ⟨y, rfl⟩ := δ.surjective x
    exact (hk y).trans (congrArg k (hP y).symm)
  · intro h
    obtain ⟨t'', ht'', hA''⟩ := stdZ_reach C _ h5.unit
    obtain rfl : t'' = t' := hinj ht'' ht' ((hZeq t'' ht'' _ hA'').trans h.symm)
    obtain ⟨k, hk⟩ := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C R' (F.R t'') _ (h1.trans (F.form_eq t)) (F.form_eq _) h5 hA''
    exact ⟨k, fun x => (hk (δ x)).trans (congrArg k (hP x))⟩

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol
open scoped nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {e : Λ →ₗ[𝓞 E] (Fin N → E)}

theorem lat_multiple (hL : IsLat (LinearMap.range e)) (v : Fin N → E) : ∃ (s : (𝓞 E)⁰) (x : Λ), s • v = e x := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E
    (LinearMap.range e : Set (Fin N → E)) v (hL.2 ▸ Submodule.mem_top)
  rw [Submodule.span_eq] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨s, x, hx.symm⟩

theorem lat_extend (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (f : Λ →ₗ[𝓞 E] (Fin N → E)) :
    ∃ g : (Fin N → E) →ₗ[E] (Fin N → E), ∀ x, g (e x) = f x := by
  have hu : ∀ s : (𝓞 E)⁰, IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) (Fin N → E)) s) := by
    have := isLocalizedModule_id (𝓞 E)⁰ (Fin N → E) E
    exact IsLocalizedModule.map_units (LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
  have : IsLocalizedModule (𝓞 E)⁰ e :=
    { map_units := hu
      surj := fun v => by
        obtain ⟨s, x, h⟩ := lat_multiple hL v
        exact ⟨(x, s), h⟩
      exists_of_eq := fun h => ⟨1, by rw [hi h]⟩ }
  exact ⟨(IsLocalizedModule.lift (𝓞 E)⁰ e f hu).extendScalarsOfIsLocalization (𝓞 E)⁰ E,
    fun x => IsLocalizedModule.lift_apply (𝓞 E)⁰ e f hu x⟩

theorem lat_matrix (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (δ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ γ : GL (Fin N) E, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := by
  obtain ⟨g, hg⟩ := lat_extend hi hL (e ∘ₗ δ.toLinearMap)
  obtain ⟨g', hg'⟩ := lat_extend hi hL (e ∘ₗ δ.symm.toLinearMap)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hg hg'
  have h1 : g ∘ₗ g' = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  have h2 : g' ∘ₗ g = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  refine ⟨⟨LinearMap.toMatrix' g, LinearMap.toMatrix' g', ?_, ?_⟩, fun x => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id]
  · show _ = LinearMap.toMatrix' g *ᵥ e x
    rw [LinearMap.toMatrix'_mulVec, hg]

omit [NumberField E] in
theorem mem_smul_range (hi : Function.Injective e) (I : Ideal (𝓞 E)) (x : Λ) :
    e x ∈ I • LinearMap.range e ↔ x ∈ I • (⊤ : Submodule (𝓞 E) Λ) := by
  rw [← Submodule.map_top, ← Submodule.map_smul'']
  exact ⟨fun ⟨y, hy, h⟩ => hi h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in
theorem congr_iff (hi : Function.Injective e) {δ : Λ ≃ₗ[𝓞 E] Λ} {γ : Matrix (Fin N) (Fin N) E}
    (h : ∀ x, e (δ x) = γ *ᵥ e x) (M : ℕ) (x : Λ) :
    (∃ y ∈ LinearMap.range e, γ *ᵥ e x = e x + M • y) ↔ ∃ y, δ x = x + M • y := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, hy⟩
    exact ⟨y, hi (by rw [h, hy, map_add (f := _), map_nsmul])⟩
  · rintro ⟨y, hy⟩
    exact ⟨e y, ⟨y, rfl⟩, by rw [← h, hy, map_add (f := _), map_nsmul]⟩

variable [IsCMField E]

theorem herm_smul_smul (G : Matrix (Fin N) (Fin N) E) (a b : E) (x y : Fin N → E) :
    herm G (a • x) (b • y) = a * cc b * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem eq_of_herm_lat (hL : IsLat (LinearMap.range e)) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, herm G (e x) (e y) = herm G' (e x) (e y)) : G = G' := by
  have h1 : ∀ u v, herm G u v = herm G' u v := fun u v => by
    obtain ⟨s, x, hx⟩ := lat_multiple hL u
    obtain ⟨t, y, hy⟩ := lat_multiple hL v
    have hs : ((s : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    have ht : ((t : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero t
    have ht' : cc ((t : 𝓞 E) : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 ht
    have e1 : e x = ((s : 𝓞 E) : E) • u := hx.symm
    have e2 : e y = ((t : 𝓞 E) : E) • v := hy.symm
    have := h x y
    rw [e1, e2, herm_smul_smul, herm_smul_smul] at this
    exact mul_left_cancel₀ (mul_ne_zero hs ht') this
  ext c d
  have e0 : ∀ G : Matrix (Fin N) (Fin N) E, herm G (Pi.single c 1) (Pi.single d 1) = G c d := fun G => by
    simp [herm, cc, Pi.single_apply, apply_ite (IsCMField.complexConj E)]
  rw [← e0 G, ← e0 G', h1]

theorem herm_eq_of_trace {ξ : E} (hξ : ξ ≠ 0) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, EFf ξ G (e x) (e y) = EFf ξ G' (e x) (e y)) (x y : Λ) : herm G (e x) (e y) = herm G' (e x) (e y) := by
  have h0 : -ξ * (herm G (e x) (e y) - herm G' (e x) (e y)) = 0 := by
    refine GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.trace_zero_of_int _ fun a => ?_
    have h1 := h (a • x) y
    have e1 : e (a • x) = (a : E) • e x := by rw [map_smul]; rfl
    have e2 : ∀ G : Matrix (Fin N) (Fin N) E, herm G ((a : E) • e x) (e y) = a * herm G (e x) (e y) := fun G => by
      have := herm_smul_smul G (a : E) 1 (e x) (e y)
      rwa [one_smul, cc, map_one, mul_one] at this
    rw [EFf, EFf, e1, e2, e2, ← sub_eq_zero, ← map_sub] at h1
    rw [← h1]
    congr 1
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left (neg_ne_zero.2 hξ))

end

theorem levelDict : LevelDict := by
  intro E _ _ _ H l D N G e ξ form hF hi hL hξ hf
  have hbij : Function.Bijective form := by
    rcases hF with rfl | rfl
    · exact D.unimod
    · exact neg_involutive.bijective.comp D.unimod
  have hpres : ∀ δ : D.La ≃ₗ[𝓞 E] D.La,
      (∀ a b, D.EF (δ a) (δ b) = D.EF a b) ↔ ∀ a b, form (δ a) (δ b) = form a b := fun δ => by
    rcases hF with rfl | rfl
    · rfl
    · simp
  have hM : 0 < l.M := by have := l.three_le; omega
  have hcong : ∀ (δ : D.La ≃ₗ[𝓞 E] D.La) (γ : Matrix (Fin N) (Fin N) E), (∀ x, e (δ x) = γ *ᵥ e x) →
      (((∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ y, δ a = a + l.M • y) ∧
        ∀ a, ∃ y, δ a = a + l.A • y) ↔
        ∀ x ∈ LinearMap.range e, γ *ᵥ x - x ∈ levIdeal l • LinearMap.range e) := fun δ γ h => by
    refine Iff.trans ?_ (levelIdeal E N (LinearMap.range e) _ l.Mb l.M l.A γ hL hM l.prod (by
      rintro _ ⟨x, rfl⟩
      exact ⟨δ x, h x⟩))
    refine and_congr ⟨fun h1 x hx => ?_, fun h1 a ha => ?_⟩ ⟨?_, fun h1 a => ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.smul_le_right hx
      exact (congr_iff hi h _ _).2 (h1 a ((mem_smul_range hi _ _).1 hx))
    · exact (congr_iff hi h _ _).1 (h1 _ ((mem_smul_range hi _ _).2 ha))
    · rintro h1 _ ⟨a, rfl⟩
      exact (congr_iff hi h _ _).2 (h1 a)
    · exact (congr_iff hi h _ _).1 (h1 _ ⟨a, rfl⟩)
  refine ⟨⟨?_, fun φ => ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨form x y, (hf x y).symm⟩
  · obtain ⟨x, hx⟩ := hbij.2 (φ.comp e.rangeRestrict.toAddMonoidHom).toIntLinearMap
    refine ⟨e x, ⟨x, rfl⟩, ?_⟩
    rintro ⟨_, y, rfl⟩
    rw [← hf, hx]
    rfl
  · rintro γ ⟨hu, hs, hc⟩
    let φ := LinearEquiv.ofInjective e hi
    let γ₀ : (Fin N → E) ≃ₗ[𝓞 E] (Fin N → E) :=
      (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv.restrictScalars (𝓞 E)
    have hγ₀ : ∀ v, γ₀ v = (γ : Matrix (Fin N) (Fin N) E) *ᵥ v := fun _ => rfl
    have hm : (LinearMap.range e).map γ₀.toLinearMap = LinearMap.range e := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hs u).1 hu
      · intro hv
        refine ⟨γ₀.symm v, (hs _).2 ?_, γ₀.apply_symm_apply v⟩
        rw [← hγ₀, γ₀.apply_symm_apply]
        exact hv
    let δ : D.La ≃ₗ[𝓞 E] D.La := φ.trans ((γ₀.ofSubmodules _ _ hm).trans φ.symm)
    have hδ : ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := fun x =>
      congrArg Subtype.val (φ.apply_symm_apply ((γ₀.ofSubmodules _ _ hm) (φ x)))
    refine ⟨δ, ⟨(hpres δ).2 fun a b => ?_, (hcong δ _ hδ).2 hc⟩, hδ⟩
    have : ((form (δ a) (δ b) : ℤ) : ℚ) = form a b := by
      rw [hf, hf, hδ, hδ, EFf, EFf, herm_mulVec', show _ * G * _ = G from hu]
    exact_mod_cast this
  · rintro δ ⟨h1, h2⟩
    obtain ⟨γ, hγ⟩ := lat_matrix hi hL δ
    refine ⟨γ, ⟨?_, fun v => ⟨?_, fun hv => ?_⟩, (hcong δ _ hγ).1 h2⟩, hγ⟩
    · refine eq_of_herm_lat hL (herm_eq_of_trace hξ fun x y => ?_)
      rw [EFf, ← herm_mulVec', ← hγ, ← hγ, ← EFf, ← hf, ← hf, (hpres δ).1 h1]
    · rintro ⟨x, rfl⟩
      exact ⟨δ x, hγ x⟩
    · obtain ⟨y, hy⟩ := hv
      refine ⟨δ.symm y, ?_⟩
      have h3 := hγ (δ.symm y)
      rw [δ.apply_symm_apply, hy] at h3
      have h4 := congrArg (fun u => ((γ⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u) h3
      simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using h4.symm

end SheetDecomposition
end
end
