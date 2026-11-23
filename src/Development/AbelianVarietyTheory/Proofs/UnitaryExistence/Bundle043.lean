module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle056
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField

theorem _root_.GlobalTheory.T.exists_unitary_conj_split_lattice_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  first | exact @GlobalTheory.UTrans.exists_isU_conj_mem | exact GlobalTheory.UTrans.exists_isU_conj_mem | (intros; apply GlobalTheory.UTrans.exists_isU_conj_mem <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem hermA_tmul_right (z : Fin n → RA F E) (t : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    hermA c G z (fun i => t ⊗ₜ[F] x i) = (t ⊗ₜ[F] (1 : E)) * hermA c G z (fv F x) := by
  simp only [hermA, fv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : sg (FiniteAdeleRing (𝓞 F) F) c (t ⊗ₜ[F] x b) = (t ⊗ₜ[F] (1 : E)) *
      sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x b) := by
    simp [sg, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h]; ring

theorem hermA_fv_fv (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp [hermA, fv, sg, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sum]

theorem adelicHermitianFormGalois_mem_of_mem_completion {S : Set (Fin n → E)} {J : Set E} {z : Fin n → RA F E}
    (hz : ∀ y ∈ S, hermA c G z (fv F y) ∈ hat1 F J) {w : Fin n → RA F E} (hw : w ∈ hat F S) :
    hermA c G z w ∈ hat1 F J := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hw
    rw [hermA_tmul_right]
    exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun a ha b hb => by
      rw [Set.mem_singleton_iff.1 ha, one_mul]; exact hb) (tmul_mem_adelicCompletion_of_integral F ht rfl) (hz x hx)
  | zero =>
    have : hermA c G z 0 = 0 := by simp [hermA]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : hermA c G z (w + w') = hermA c G z w + hermA c G z w' := by
      simp only [hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : hermA c G z (-w) = - hermA c G z w := by
      simp only [hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
    rw [this]; exact neg_mem h

end

theorem latOf_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → (∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y) → ∀ v : Fin n → E, (∀ y ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L := by
  intro F E _ _ _ _ _ n L c G J g hfg hspan hc hG hdet hJ hL hg v
  have hd := GlobalTheory.T.adelicCompletion_selfDual_of_selfDual_lattice F E n L c G J hfg hspan hc hG hdet hJ hL
  obtain ⟨Λ, hΛ, -, -, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hfg hspan
  constructor
  · intro hv
    have hz : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ
        (((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F v) = fv F v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨_, (hd _).1 fun y hy => ?_, hz⟩
    rw [← hg, hz]
    refine adelicHermitianFormGalois_mem_of_mem_completion c G (S := (Λ : Set (Fin n → E))) (fun y' hy' => ?_) ?_
    · rw [hermA_fv_fv]
      exact one_tmul_mem_adelicCompletionOfElementSet F (hv y' (hΛ ▸ hy'))
    · have : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F y ∈
          (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) := by
        rw [hhat]
        exact ⟨fv F y, AddSubgroup.subset_closure ⟨1, adele_one_integral F, y, hy, rfl⟩, rfl⟩
      exact this
  · rintro ⟨z, hz, hzv⟩ y ⟨w, hw, hwy⟩
    rw [← one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, ← hermA_fv_fv, ← hzv, ← hwy, hg]
    exact adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hw

end GlobalTheory.AdLat
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem exists_framePeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hg hb hn k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hg hb hn k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hφa : ∀ a, φ a = (M.φ k a : Fin r → E) := fun a => rfl
  obtain ⟨-, hφ'⟩ := hφ φ hφa
  have hemb : ∀ (τ : E →+* ℂ) (v w : Fin r → E), Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by
    intro τ v w
    funext a
    simp [Data.emb]
  let Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)) := fun x =>
    AddMonoidHom.mk' (fun a j => perFr (M.X k) x (φ a) (relab c σ (e j).1) (e j).2) (by
      intro a b
      funext j
      simp only [Pi.add_apply, hper, map_add (f := _), hemb]
      split_ifs
      · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      · rw [Matrix.mulVec_add, Pi.add_apply])
  have hPf : IsPerFr e F M k Pf := fun x a j => rfl
  have hPf' : ∀ x v j, Pf x v j = if ((idx j).2 : ℕ) < (F.Di k).q then
      hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ v))
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ v)) (idx j).2 :=
    fun x v j => (hPf x v j).trans (hper x _ j)
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by rw [← hp0]
  obtain ⟨h1, h2⟩ := GlobalTheory.periods_eq_frame_periods E H Dw l Xo _ g _ F k r _ (M.X k).Gm φ (M.X k).Ψ idx Pf
    (hb.type k).2 hty hξ hpos hφ' hr hPf'
  have h3 := (GlobalTheory.per_move E H (F.Di k) r _ (M.X k).Gm φ (M.X k).Ψ (hb.type k).2 g idx _ hty hξ hpos hφ').1
    Pf hPf'
  rw [hdom]
  refine ⟨Pf, hPf, fun Pf' h' => ?_, fun x hx => (h1 x hx).1, h3, h2⟩
  funext x
  exact AddMonoidHom.ext fun a => funext fun j => (h' x a j).trans (hPf x a j).symm

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by
  set L : Submodule ℤ V := P.range.toIntSubmodule with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩
  let b := Module.Free.chooseBasis ℤ L
  let e : A ≃+ P.range := AddMonoidHom.ofInjective hi
  let r : V →ₗ[ℝ] W := (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))
  refine ⟨r, fun a => ?_⟩
  let f₁ : L →+ W := r.toAddMonoidHom.comp L.subtype.toAddMonoidHom
  let f₂ : L →+ W := Q.comp e.symm.toAddMonoidHom
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show r (b i : V) = Q (e.symm (b i))
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i
  have h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩) := LinearMap.congr_fun hf ⟨P a, a, rfl⟩
  have he : e.symm ⟨P a, a, rfl⟩ = a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h, he]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.CompRat.exists_complex_linear_of_pure_types : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La), _root_.GlobalTheory.CompRat.IsSplit hP → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP H.rt0, Φ a ∈ _root_.GlobalTheory.PureType.lat hP' H.rt0) → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP (-H.rt0), Φ a ∈ _root_.GlobalTheory.PureType.lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂
  have hP₀ := hP
  have hP'₀ := hP'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀
  obtain ⟨-, hi, hd, hs, -⟩ := hP₀
  obtain ⟨-, hi', hd', hs', -⟩ := hP'₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs'
    (P.comp Φ.symm.toLinearMap.toAddMonoidHom)
  have hr₁ : ∀ a, r (P a) = P' (Φ a) := hr
  have hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b) := hr'
  have him : H.rt0.im ≠ 0 := by
    intro h0
    have hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2 := by simp [pow_two, Complex.mul_re, h0]
    rw [H.sqrt_neg_disc_sq] at hsq
    have h2 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp at hsq
    nlinarith [sq_nonneg H.rt0.re]
  have hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤ :=
    hsplit
  have hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)
    have ry : r (H.rt0 • P y) = H.rt0 • r (P y) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]
    have rz : r (-H.rt0 • P z) = -H.rt0 • r (P z) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]
    have rz' : r (H.rt0 • P z) = H.rt0 • r (P z) := by
      rw [neg_smul, map_neg, neg_smul, neg_inj] at rz
      exact rz
    simp only [map_add (f := _), smul_add, ry, rz']
  have hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    have hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r :=
      LinearMap.ext_on_range hs fun a => by simpa using hkey a
    intro v
    simpa using LinearMap.congr_fun hext v
  have hlin : ∀ (c : ℂ) v, r (c • v) = c • r v := by
    intro c v
    have hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) +
        ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0 := by
      apply Complex.ext <;> simp <;> field_simp <;> ring
    rw [hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add (f := _), map_smul, map_smul,
      hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl : ∀ v, r' (r v) = v := by
    have hext : r'.comp r = LinearMap.id :=
      LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]
    exact fun v => LinearMap.congr_fun hext v
  have hrr : ∀ w, r (r' w) = w := by
    have hext : r.comp r' = LinearMap.id :=
      LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]
    exact fun w => LinearMap.congr_fun hext w
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r, map_add' := r.map_add, map_smul' := hlin }
  exact ⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl,
    fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩

end GlobalTheory.CompRat
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

namespace GlobalTheory.PeriodFormCompare

variable {R : Type} [CommRing R] [IsDomain R]

theorem generic_val (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) = algebraMap R (FractionRing R) r := by
  have e : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [e]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (jK R).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

theorem psiCoord_iff (D : DegPre R) (χ : D.X) (r : R) :
    PsiCoord D χ r ↔ ∃ x, IsPsiCoord D χ x ∧ x.val = algebraMap R (FractionRing R) r := by
  constructor
  · rintro ⟨j, hj, h, e⟩
    exact ⟨_, ⟨j, h, hj, rfl⟩, (congrArg _ e.symm).trans (generic_val r)⟩
  · rintro ⟨_, ⟨j, h, hj, rfl⟩, e⟩
    refine ⟨j, hj, h, ?_⟩
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
      ((generic_val r).trans e.symm)

theorem isPsiCoord_toUnitK {D : DegPre R} {χ : D.X} {r : R} (h : PsiCoord D χ r) (h0 : r ≠ 0) :
    IsPsiCoord D χ (toUnitK r h0) := by
  obtain ⟨x, hx, e⟩ := (psiCoord_iff D χ r).1 h
  have : x = toUnitK r h0 := Units.ext e
  exact this ▸ hx

theorem exists_psiCoord_iff [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    (∃ r, PsiCoord D χ r) ↔ D.PsiIn χ ⊤ := by
  constructor
  · rintro ⟨r, hr⟩
    exact (PeriodFormEdge.psiIn_iff hr ⊤).2 trivial
  · intro hI
    obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D χ
    have h := PsiCoordLocal.generic_le D χ j hj
    obtain ⟨s, -, e⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
    exact ⟨r, j, hj, h, e⟩

theorem exists_psiCoord_of_isPsiCoord [IsLocalRing R] {D : DegPre R} {χ : D.X} (hI : D.PsiIn χ ⊤)
    {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    ∃ r, PsiCoord D χ r ∧ x.val = algebraMap R (FractionRing R) r := by
  obtain ⟨r, hr⟩ := (exists_psiCoord_iff D χ).2 hI
  obtain ⟨y, hy, e⟩ := (psiCoord_iff D χ r).1 hr
  obtain ⟨u, hu⟩ := hx.unique hy
  have : x.val = algebraMap R (FractionRing R) (u * r) := by
    rw [hu, map_mul, ← e]; rfl
  exact ⟨u * r, (psiCoord_iff D χ _).2 ⟨x, hx, this⟩, this⟩

theorem psiIn_top {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) : D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h; exact (PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

section DVR

variable [IsDiscreteValuationRing R]

end DVR

section At

variable [IsLocalRing R] {C : Type} [NormedField C]


variable {φ : FractionRing R →+* C}

end At

end GlobalTheory.PeriodFormCompare
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.betaAt_add_left_and_diag_eq_two_order : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord Dg.toPre χ r → f r ≠ 0) → (∀ a a' b, betaAt Dg.toPre f p (a + a') b = betaAt Dg.toPre f p a b + betaAt Dg.toPre f p a' b) ∧ ∀ a, betaAt Dg.toPre f p a a = 2 * vPsiAt Dg.toPre f p a := by
  first | exact @GlobalTheory.BetaAdd.main | exact GlobalTheory.BetaAdd.main | (intros; apply GlobalTheory.BetaAdd.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier : ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  first | exact @GlobalTheory.SmallClosedField.exists_embedding_and_extension | exact GlobalTheory.SmallClosedField.exists_embedding_and_extension | (intros; apply GlobalTheory.SmallClosedField.exists_embedding_and_extension <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isHolTo_fibPt_and_comp_fibre : ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) := by
  first | exact @GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | exact GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | (intros; apply GlobalTheory.HolFibre.isHolTo_fibPt_and_comp <;> assumption)
end
