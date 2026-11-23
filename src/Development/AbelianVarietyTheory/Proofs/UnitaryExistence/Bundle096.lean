module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRead

open GlobalTheory.CharRead

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}



theorem exists_rat_finCong_of_marks (l : Level H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (t : Dw.La → La)
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : La ≃ₗ[𝓞 D.host.E] Λ) (φ' : La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (t a) : Fin V.rank → D.host.E) - (finHom V g).1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (t a) : Fin V.rank → D.host.E) - (finHom V g').1.mulVec (finVec V (io a)) =
        (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hΛ hΛ'
  obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_unitary_of_trace_eq _ _ (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V g').2.1
    φ φ' _ ξ hξ htr
  obtain ⟨γ, hγ⟩ := r3 δ hδ3
  obtain ⟨m1, m2⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ δ g hγ
  have hlat : latG V (γ * g) = latG V g' := by
    ext v
    have hv : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have a1 := m1 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    have a2 := hδ2 (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)
    rw [hv] at a1 a2
    exact a1.symm.trans a2
  have hc : FinCong V l.M ((γ * g)⁻¹ * g') := by
    refine finCong_of_marks l V io hio _ _ hlat (fun a => finVec V (φ' (t a) : Fin V.rank → D.host.E)) ?_ hM'
    intro a ha
    obtain ⟨w, hw, e⟩ := hM a ha
    refine ⟨_, (m2 w).1 hw, ?_⟩
    have e2 := congrArg (fun z => (finHom V γ).1 *ᵥ z) e
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul] at e2
    rw [(r5 _ δ hγ).1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hδ1] at e2
    exact e2
  have hu : gLat V ((γ * g)⁻¹ * g') = latHat V := by
    refine gLat_eq_of_finCong V _ ((GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat) ?_
    have e0 : ((γ * g)⁻¹ * g')⁻¹ = g'⁻¹ * (γ * g) := by group
    rw [e0]
    exact (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.2.2 _ _ hlat.symm
  exact ⟨γ, (r1 γ).2 ⟨δ, hγ⟩, _, hu, hc, (mul_inv_cancel_left _ _).symm⟩

theorem exists_rat_finCong_of_index {l : Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {n : ℕ}
    {ty : Fin n → D.host.E →+* ℂ}
    (F : FamilyUnif Xo s ty) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hio : LatEmb V io) (i i' : Fin F.n) (hi : i = i')
    (g g' : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : Λ = latG V g) (hΛ' : Λ' = latG V g')
    (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] Λ) (φ' : (F.Di i').La ≃ₗ[𝓞 D.host.E] Λ') (ξ : D.host.E) (hξ : ξ ≠ 0)
    (htr : ∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ a : Fin V.rank → D.host.E) (φ b)))
    (htr' : ∀ a b, (((F.Di i').EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (ξ * herm (-V.gramᵀ) (φ' a : Fin V.rank → D.host.E) (φ' b)))
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g, finVec V (φ (F.t i a) : Fin V.rank → D.host.E) -
        (finHom V g).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w)
    (hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V g', finVec V (φ' (F.t i' a) : Fin V.rank → D.host.E) -
        (finHom V g').1.mulVec (finVec V (io a)) = (l.M : ℕ) • w) :
    ∃ γ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ FinCong V l.M u ∧ g' = γ * g * u := by
  subst hi
  exact exists_rat_finCong_of_marks l V io hio (F.t i) g g' Λ Λ' hΛ hΛ' φ φ' ξ hξ
    (fun a b => (htr a b).symm.trans (htr' a b)) hM hM'


end GlobalTheory.CompRead
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ClassUniq

lemma isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h1 := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  unfold IsHolTo at h1 ⊢
  intro U f
  obtain ⟨ho, hd⟩ := h1 U f
  have hj : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := continuous_const.prodMk continuous_id
  have hjd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hset : {b | b ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (fun z => (F.ex k P z).left) b ⁻¹ᵁ U} =
      (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
        {b | b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) ∧
          ⊤ ≤ (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (F.ex k P bz.2).left) b ⁻¹ᵁ U} := by
    ext z
    simp
  rw [hset]
  refine ⟨ho.preimage hj, ?_⟩
  have h2 := hd.comp (s := (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
      {b | b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) ∧
        ⊤ ≤ (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (F.ex k P bz.2).left) b ⁻¹ᵁ U})
    hjd.differentiableOn (fun _ hz => hz)
  rw [Function.comp_def] at h2
  dsimp only at h2 ⊢
  exact h2

lemma isPeriod_comp_isometry {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (hg : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P') :
    IsPeriod D ty (P'.comp gam.toLinearMap.toAddMonoidHom) := by
  unfold IsPeriod at hP ⊢
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P'.comp gam.toLinearMap.toAddMonoidHom).range = P'.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨gam.symm b, by simp⟩
  have hr2 : Set.range (P'.comp gam.toLinearMap.toAddMonoidHom) = Set.range P' := by
    rw [← AddMonoidHom.coe_range, ← AddMonoidHom.coe_range, hrange]
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x i
    show P' (gam (a • x)) i = (ty i) (a : E) * P' (gam x) i
    rw [map_smul]
    exact hlin a (gam x) i
  · intro a b hab
    exact gam.injective (hinj hab)
  · rw [hrange]
    exact hdisc
  · rw [hr2]
    exact hspan
  · intro x y
    have h := him (gam x) (gam y)
    rw [hg] at h
    exact h

theorem eq_of_matched : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : _root_.GlobalTheory.FrameUnif.ModelsOf F r) (k k' : Fin F.n) (γ : GL (Fin r) E), 1 ≤ Dw.p + Dw.q → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (M.X k').Gm = (M.X k).Gm → (M.X k').ξ0 = (M.X k).ξ0 → (∀ u v, herm (M.X k).Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm (M.X k).Gm u v) → (∀ v, v ∈ (M.X k).Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k').Λ) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.M • w) → (∀ a, ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.A • w) → k = k' := by
  intro hT hL E _ _ _ H Dw l Xo σ' g ty F r M k k' γ hpq hρ hty hMB hGm hξ hunit hΛ hcM hcA
  have hmem : ∀ a : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((M.φ k a : (M.X k).Λ) : Fin r → E) ∈ (M.X k').Λ :=
    fun a => (hΛ _).1 (M.φ k a).2
  let gmap : (F.Di k).La →ₗ[𝓞 E] (F.Di k').La :=
    (M.φ k').symm.toLinearMap ∘ₗ LinearMap.codRestrict (M.X k').Λ
      (((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) ∘ₗ
        (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun a => hmem a)
  have hgmap : ∀ a, ((M.φ k' (gmap a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    simp only [gmap, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have hinv : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.inv_mul γ
  have hinv' : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.mul_inv γ
  have hinj : Function.Injective gmap := by
    intro a b hab
    have h1 := congrArg (fun x => ((M.φ k' x : (M.X k').Λ) : Fin r → E)) hab
    simp only [hgmap] at h1
    have h2 := congrArg (fun v => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2
    exact (M.φ k).injective (Subtype.ext h2)
  have hsurj : Function.Surjective gmap := by
    intro b
    have hAv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E)) = ((M.φ k' b : (M.X k').Λ) : Fin r → E) := by
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    have hvmem : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E) ∈ (M.X k).Λ := by
      rw [hΛ, hAv]
      exact (M.φ k' b).2
    refine ⟨(M.φ k).symm ⟨_, hvmem⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgmap, LinearEquiv.apply_symm_apply]
    exact hAv
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La := LinearEquiv.ofBijective gmap ⟨hinj, hsurj⟩
  have hgam : ∀ a, ((M.φ k' (gam a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := fun a => hgmap a
  have hiso : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b := by
    intro a b
    have h1 := hMB.ef k' (gam a) (gam b)
    have h2 := hMB.ef k a b
    rw [hgam, hgam, hGm, hξ, hunit] at h1
    exact_mod_cast h1.trans h2.symm
  have hcM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ x, gam (F.t k a) = F.t k' a + l.M • x := by
    intro a ha
    obtain ⟨w, hw, hweq⟩ := hcM a ha
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have hcA' : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x := by
    intro a
    obtain ⟨w, hw, hweq⟩ := hcA a
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have htyk' : IsTypeFn H (F.Di k').p (F.Di k').q ty := by
    rw [(F.sig k').1, (F.sig k').2]
    exact hty
  obtain ⟨P', hP'⟩ := (GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty htyk').2
  have hP := isPeriod_comp_isometry gam hiso hP'
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H Dw l Xo σ' g ty hpq hρ hty
    (F.Di k) (F.Di k') (F.t k) (F.t k') (P'.comp gam.toLinearMap.toAddMonoidHom) P'
    (F.u k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.u k' P')
    (F.ex k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.ex k' P')
    ⟨F.over_σ k _ hP, hP, ⟨F.ex_add k _ hP, F.ex_onto k _ hP, isHolTo_ex F k _ hP, (F.ex_diff k _ hP).1,
      (F.ex_diff k _ hP).2⟩, F.ex_ker k _ hP, F.ex_lin k _ hP, F.ex_weil k _ hP, F.ex_eta k _ hP,
      F.ex_etaA k _ hP⟩
    ⟨F.over_σ k' _ hP', hP', ⟨F.ex_add k' _ hP', F.ex_onto k' _ hP', isHolTo_ex F k' _ hP',
      (F.ex_diff k' _ hP').1, (F.ex_diff k' _ hP').2⟩, F.ex_ker k' _ hP', F.ex_lin k' _ hP',
      F.ex_weil k' _ hP', F.ex_eta k' _ hP', F.ex_etaA k' _ hP'⟩
  have hu := key.2 ⟨gam, LinearEquiv.refl ℂ _, hiso, hcM', hcA', fun a => rfl⟩
  exact F.disj k k' _ _ hP hP' hu

end GlobalTheory.ClassUniq
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := h0
  have himg : ∀ x : Fin n → M, x '' {b | b.val < r} = Set.range (fun b : Fin r => x (Fin.castLE hrn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hrn b, b.2, rfl⟩
  have hadj1 : adj 1 = 1 := by
    have := hadj 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  let f : (Fin r → M) → F := fun z =>
    if h : Submodule.span R (Set.range z) = ⊤ then (((ψ (adj (h1 y z hy h).exists.choose))⁻¹ : Fˣ) : F) else 0
  have hf : ∀ (z : Fin r → M) (g : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ → (∀ b, g (y b) = z b) →
      f z = (((ψ (adj g))⁻¹ : Fˣ) : F) := by
    intro z g hz hg
    have : (h1 y z hy hz).exists.choose = g :=
      (h1 y z hy hz).unique (h1 y z hy hz).exists.choose_spec hg
    simp only [f, dif_pos hz, this]
  have hspan : ∀ (z : Fin r → M) (k : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ →
      Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
    intro z k hz
    have e : (Set.range fun b => k (z b)) = (k : M →ₗ[R] M) '' Set.range z := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hz, Submodule.map_top, LinearEquiv.range]
  let x₀ : Fin n → M := fun b => if h : b.val < r then y ⟨b.val, h⟩ else 0
  have hx₀ : (fun b : Fin r => x₀ (Fin.castLE hrn b)) = y := by
    funext b
    simp [x₀]
  refine ⟨fun x => f (fun b => x (Fin.castLE hrn b)), x₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' h
    have : (fun b : Fin r => x (Fin.castLE hrn b)) = fun b => x' (Fin.castLE hrn b) :=
      funext fun b => h _ b.2
    simp only [this]
  · intro x hx
    rw [himg]
    by_contra hz
    exact hx (by simp only [f, dif_neg hz])
  · intro k x
    set z : Fin r → M := fun b => x (Fin.castLE hrn b) with hzdef
    change f (fun b => k (z b)) = _ * f z
    by_cases hz : Submodule.span R (Set.range z) = ⊤
    · obtain ⟨g, hg, -⟩ := h1 y z hy hz
      rw [hf z g hz hg, hf _ (k * g) (hspan z k hz) (fun b => by simp [hg b]), hadj, map_mul, mul_inv,
        Units.val_mul, mul_comm]
    · have hz' : ¬ Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
        intro h
        have := hspan _ k.symm h
        simp only [LinearEquiv.symm_apply_apply] at this
        exact hz this
      simp only [f, dif_neg hz, dif_neg hz', mul_zero]
  · change f (fun b : Fin r => x₀ (Fin.castLE hrn b)) = 1
    rw [hx₀, hf y 1 hy (fun b => rfl), hadj1]
    simp
  · rw [himg, hx₀, hy]

theorem exists_phiPin_of_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → Dw.p + Dw.q ≤ n → ∀ ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, ∃ (φ : (Fin n → LevQ Dw d.l₂) → c.F) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d), DeltaDat.PhiPin { d with φδ := φ } ph ψ x₀ := by
  intro E _ _ _ H Dw l Xo c n d hd hn ψ
  obtain ⟨h0, h1, adj, hadj, hiff⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨ph, x₀, ha, hb, hc, hd1, hd2⟩ :=
    exists_equivariant_fun_on_spanning_families hn h0 h1 adj hadj ψ
  refine ⟨fun q => d.eF.symm (∑ᶠ x : Fin n → LaJ Xo c d, d.eF (ph x) *
      ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))), ph, x₀, ha, hb, ?_, hd1, hd2, ?_⟩
  · intro k kst h x
    have := (hiff k kst).mp h
    subst this
    exact hc kst x
  · intro q
    exact d.eF.apply_symm_apply _

end GlobalTheory
end
