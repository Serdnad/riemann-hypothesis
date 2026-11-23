module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle979
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqConstMulOfNormOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle619
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle984
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle014

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverConstAt



theorem rel_at : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h₀ : GA D (T.V j σ)) (γ : GL (Fin D.R.r) D.host.E), (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp), (C.dict₂ h₀).1 = k₂ → (T.dict j σ h₀).1 = k → ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x' := by
  intro D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr k₂ k hk₂ hk x x' hx hxx'
  subst hk₂ hk
  have hU := hT.unf j hj σ hσ
  have hU₂ := hC.2.2.2.1
  have hΨ : ∀ τ, τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ :=
    fun τ => ((hU.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hx' : x' ∈ ((T.U j σ).X (T.dict j σ h₀).1).dom :=
    GlobalTheory.FrameDom.mem_dom_of_isometry _ _ _ _ γ ((hU.2.1 _).1.trans (hU₂.2.1 _).1.symm) hΨ hiso x x' hx hxx'
  obtain ⟨o₁, o₂⟩ := GlobalTheory.T.coverFramedPoint_over_moved_base_frame D T hT j hj σ hσ C hC h₀ γ hΛ hiso hfr x x' hx hx' hxx'
  obtain ⟨t, ht, hn, hr⟩ := GlobalTheory.CoverFrameMod.exists_scalar C hC.2.2.1 _ _ o₁ o₂
  refine ⟨hx', t, ht, fun hd => ?_, fun n a _ f hf f₂ _ hp => ?_⟩
  · have hd' : ∀ τ i, ‖dmin ((T.U j σ).X (T.dict j σ h₀).1).Gm x' τ i‖ = 1 := by
      rintro ⟨τ, h₁⟩ i
      rw [← hd ⟨τ, (hΨ τ).1 h₁⟩ i]
      unfold dmin
      rw [hxx' τ ((hΨ τ).1 h₁) h₁, GlobalTheory.FrameDom.gram_mul _ _ _ hiso τ]
    obtain ⟨g, e, F, ik, φ, -, hP⟩ := hU.2.2.2.2.2
    obtain ⟨g₂, e₂, F₂, ik₂, φ₂, -, hP₂⟩ := hU₂.2.2.2.2.2
    obtain rfl : g₂ = g := Fin.equiv_iff_eq.1 ⟨e₂.trans e.symm⟩
    obtain ⟨P, -, p, u, -, N⟩ := hP _ ⟨x', hx'⟩
    obtain ⟨P₂, -, p₂, u₂, -, N₂⟩ := hP₂ _ ⟨x, hx⟩
    exact hn _ _ _ _ _ F F₂ _ _ P P₂ p p₂ u u₂ (N hd') (N₂ hd)
  · have e : rdU (T.U j σ) f (T.dict j σ h₀).1 x' =
        toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un (T.dict j σ h₀).1 ⟨x', hx'⟩)) := dif_pos hx'
    rw [e]
    exact (dif_pos hx).trans (hr n a f hf f₂ hp)

end GlobalTheory.CoverConstAt

namespace GlobalTheory.CoverConstAt



theorem const_of_rel : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∀ (k₂ : C.U₂.Comp) (k : (T.U j σ).Comp) (γ : GL (Fin D.R.r) D.host.E), (∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k).dom ∧ ∃ t : ℂ, t ≠ 0 ∧ ((∀ τ i, ‖dmin (C.U₂.X k₂).Gm x τ i‖ = 1) → ‖t‖ = 1) ∧ ∀ n : ℕ, ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k x') → ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ k' : (T.U j σ).Comp, k = k' → ∀ (x : Frame (C.U₂.X k₂).Ψ D.R.r) (x' : Frame ((T.U j σ).X k').Ψ D.R.r), x ∈ (C.U₂.X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k').Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ ((T.U j σ).X k').dom ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k' x' := by
  intro D T hL j hj σ hσ C hC n k₂ k γ hx
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ : Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ := by
    intro x τ h₂ h₁
    rfl
  have hGdom : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom := fun x hx' => (hx x (G x) hx' (hGrel x)).1
  have hGdiff : Differentiable ℂ G := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [G, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    fun_prop
  let ι := {p : ((D.host.E →+* ℂ) × ℕ → ℕ) × Rul (T.Q.Xo j) T.Q.c × Rul C.d.Xo₂ C.d.c₂ //
    Dom p.1 n ∧ p.2.1 ∈ sec (T.Q.Xo j) T.Q.c p.1 n ∧ p.2.2 ∈ sec C.d.Xo₂ C.d.c₂ p.1 n ∧ C.IsPull p.2.1 p.2.2}
  let P₂ : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i => rdU C.U₂ i.1.2.2 k₂
  let P : ι → Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun i x => rdU (T.U j σ) i.1.2.1 k (G x)
  have hP₂d : ∀ i, DifferentiableOn ℂ (P₂ i) (C.U₂.X k₂).dom := fun i =>
    (hU₂.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.2 i.2.2.2.1 k₂).1
  have hPd : ∀ i, DifferentiableOn ℂ (P i) (C.U₂.X k₂).dom := fun i =>
    (hU₁.2.2.2.2.1 i.1.1 n i.2.1 i.1.2.1 i.2.2.1 k).1.comp hGdiff.differentiableOn hGdom
  have hg : ∀ x ∈ (C.U₂.X k₂).dom, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i : ι, P₂ i x = c * P i x := by
    intro x hxd
    obtain ⟨b, hb, hyd, hyo⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_borel_orthonormal_move (C.U₂.X k₂) hxd
    obtain ⟨-, t, -, hmod, hrel⟩ := hx (rmul x b) (G (rmul x b)) hyd (hGrel _)
    have ht1 : ‖t‖ = 1 := hmod (fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_diagonal_minor_one _ hyo τ i)
    refine ⟨t ^ n, by rw [norm_pow, ht1, one_pow], ?_⟩
    rintro ⟨⟨a, f, f₂⟩, hDom, hf, hf₂, hP⟩
    let b₁ : Frame ((T.U j σ).X k).Ψ D.R.r := fun τ => b ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have hb₁ : b₁ ∈ Bor ((T.U j σ).X k).Ψ D.R.r := fun τ => hb ⟨τ.1, (hΨ τ.1).2 τ.2⟩
    have e1 := hrel n a hDom f hf f₂ hf₂ hP
    have e2 : rdU C.U₂ f₂ k₂ (rmul x b) = bchar (laU C.U₂ a n k₂) b * rdU C.U₂ f₂ k₂ x :=
      (hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂).2.1 x hxd b hb
    have e3 : G (rmul x b) = rmul (G x) b₁ := by
      funext τ
      simp only [G, rmul, b₁, mat]
      exact (Matrix.mul_assoc ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1) (mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩) (mat b ⟨τ.1, (hΨ τ.1).2 τ.2⟩)).symm
    have e4 : rdU (T.U j σ) f k (rmul (G x) b₁) = bchar (laU (T.U j σ) a n k) b₁ * rdU (T.U j σ) f k (G x) :=
      (hU₁.2.2.2.2.1 a n hDom f hf k).2.1 (G x) (hGdom x hxd) b₁ hb₁
    have e5 : bchar (laU C.U₂ a n k₂) b = bchar (laU (T.U j σ) a n k) b₁ := by
      unfold bchar
      refine Fintype.prod_equiv (Equiv.subtypeEquivRight (fun τ => hΨ τ)) _ _ (fun τ => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hla a n τ.1 τ.2 ((hΨ τ.1).1 τ.2) i]
      rfl
    have e6 : bchar (laU C.U₂ a n k₂) b ≠ 0 := by
      unfold bchar
      refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
      have hdet : (mat b τ).det ≠ 0 := (hb τ).1
      rw [Matrix.det_of_upperTriangular (M := mat b τ) (fun a c h => (hb τ).2 a c h)] at hdet
      simpa [mat] using Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    show rdU C.U₂ f₂ k₂ x = t ^ n * rdU (T.U j σ) f k (G x)
    apply mul_left_cancel₀ e6
    rw [← e2, e1, e3, e4, ← e5]
    ring
  classical
  let g : Frame (C.U₂.X k₂).Ψ D.R.r → ℂ := fun x => if h : x ∈ (C.U₂.X k₂).dom then (hg x h).choose else 1
  have hg1 : ∀ x ∈ (C.U₂.X k₂).dom, ‖g x‖ = 1 := fun x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.1
  have hgr : ∀ i, ∀ x ∈ (C.U₂.X k₂).dom, P₂ i x = g x * P i x := fun i x h => by
    simp only [g, dif_pos h]; exact (hg x h).choose_spec.2 i
  obtain ⟨u, hu1, hu⟩ := GlobalTheory.CoverConst.eq_const_mul_of_norm_one (C.U₂.X k₂).dom (ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected D.R.r (C.U₂.X k₂)).isPreconnected P₂ P g hP₂d hPd hg1 hgr
  refine ⟨u, hu1, ?_⟩
  rintro k' rfl x x' hxd hrel'
  refine ⟨(hx x x' hxd hrel').1, ?_⟩
  have hx' : x' = G x := by
    funext τ
    exact hrel' τ.1 ((hΨ τ.1).2 τ.2) τ.2
  intro a hDom f hf f₂ hf₂ hP
  rw [hx']
  exact hu ⟨(a, f, f₂), hDom, hf, hf₂, hP⟩ x hxd

end GlobalTheory.CoverConstAt

namespace GlobalTheory.CoverConstAt



theorem cover_read_const : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ u : C.U₂.Comp → ℂ, (∀ k, ‖u k‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → ∀ h : GA D (T.V j σ), rdU C.U₂ f₂ (C.dict₂ h).1 (C.dict₂ h).2 = u (C.dict₂ h).1 * rdU (T.U j σ) f (T.dict j σ h).1 (T.dict j σ h).2 := by
  intro D T hL j hj σ hσ C hC n
  have hU := hL.unf j hj σ hσ
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  choose h₀ hh₀ using GlobalTheory.CoverOnto.exists_dict₂_comp D T hL j hj σ hσ C hC
  have hframes := fun k₂ : C.U₂.Comp => GlobalTheory.CoverFrameMove.frames_differ D T hL j hj σ hσ C hC (h₀ k₂)
  choose γ₀ hΛ hiso hfr using hframes
  have hconst := fun k₂ : C.U₂.Comp => const_of_rel D T hL j hj σ hσ C hC n k₂ (T.dict j σ (h₀ k₂)).1 (γ₀ k₂)
    (rel_at D T hL j hj σ hσ C hC (h₀ k₂) (γ₀ k₂) (hΛ k₂) (hiso k₂) (hfr k₂) k₂ _ (hh₀ k₂) rfl)
  choose u hu1 hu using hconst
  refine ⟨u, hu1, ?_⟩
  intro a hDom f hf f₂ hf₂ hP h
  have e₂ : (C.dict₂ h).1 = (C.dict₂ (h₀ (C.dict₂ h).1)).1 := (hh₀ _).symm
  have e₁ : (T.dict j σ (h₀ (C.dict₂ h).1)).1 = (T.dict j σ h).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hL j hj σ hσ C hC _ h (hh₀ _)
  obtain ⟨δ, hδ, hδrel⟩ := GlobalTheory.T.frame_base_eq_cover_frame_moved_by_arithmetic D T hL j hj σ hσ C hC h (h₀ (C.dict₂ h).1) e₂ (γ₀ _) (hΛ _) (hiso _) (hfr _)
  have hΨ : ∀ τ, τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ ↔ τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ :=
    fun τ => ((hU₂.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm
  let x' : Frame ((T.U j σ).X (T.dict j σ h).1).Ψ D.R.r := fun τ =>
    ((γ₀ (C.dict₂ h).1 : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat (C.dict₂ h).2 ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hxd : (C.dict₂ h).2 ∈ (C.U₂.X (C.dict₂ h).1).dom := hC.2.2.2.2.1 h
  obtain ⟨hx'd, hr⟩ := hu (C.dict₂ h).1 _ e₁ (C.dict₂ h).2 x' hxd (fun τ h₂ h₁ => rfl)
  have hd : (T.dict j σ h).2 = lact δ x' := by
    funext τ
    exact hδrel τ.1 ((hΨ τ.1).2 τ.2) τ.2
  rw [hr a hDom f hf f₂ hf₂ hP, hd, (hU.2.2.2.2.1 a n hDom f hf _).2.2 δ hδ x' hx'd,
    hL.chiTriv j hj σ hσ a n hDom _ δ hδ, one_mul]

end GlobalTheory.CoverConstAt
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct




namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}



theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
end
