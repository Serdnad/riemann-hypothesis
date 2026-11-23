module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle060
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Flags

theorem isExtOver_mk (Ω K E : Type) [Field Ω] [Field K] [Algebra Ω K] [AddCommGroup E] [Module Ω E] :
    IsExtOver (algebraMap Ω K) (TensorProduct.mk Ω K E 1).toAddMonoidHom := by
  refine ⟨fun a e => ?_, fun n b hb => ?_⟩
  · show (1 : K) ⊗ₜ[Ω] (a • e) = algebraMap Ω K a • ((1 : K) ⊗ₜ[Ω] e)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · exact Module.Flat.linearIndependent_one_tmul hb

theorem pull_isFlagVB_genB : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom).IsFlagVBOn Set.univ (genB c s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hx hgen hVB hTw hc hx' hgen' hd hch s p' _
  classical
  obtain ⟨⟨c₁, J⟩, hcJ⟩ := hx'.cover p'
  obtain ⟨hx0, hchart, hmin⟩ := GlobalTheory.T.flag_chart_generic_field Ω E κ x S r n φ c X' ξ' p' c₁ J hcJ
  obtain ⟨hfp, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd p'
  have hInC : InChart ξ x c₁ ⟨f p'.1, hfp⟩ := (hch p' c₁ hfp).2 hchart
  obtain ⟨U, hU, β₀, hspan, hfr⟩ := hVB s ⟨f p'.1, hfp⟩ trivial
  have hfr0 := hfr ⟨f p'.1, hfp⟩ trivial hU
  obtain ⟨B₀, hBreg, hAreg, hBA⟩ := GlobalTheory.T.frame_coeffs_regular_in_chart X Ω ξ E κ x (L s) (m s) (n s) (r s) (φ s) (hTw s) _ c₁ hInC β₀ hfr0
  have hxΩ : x c₁ ≠ 0 := hInC.1
  have hCex : ∀ l, ∃ C : Fin (r s) → Ω, c s l = ∑ a, C a • β₀ a := by
    intro l
    have : c s l ∈ Submodule.span Ω (Set.range β₀) := by
      rw [hspan, ← (hc s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
    exact ⟨C, hC.symm⟩
  choose C hC using hCex
  set ι := algebraMap Ω (GenField Ω r) with hι
  let A₀ : Matrix (Fin (n s)) (Fin (r s)) Ω := Matrix.of (fun j a => φ s j (β₀ a) / x c₁ ^ m s)
  let A : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := A₀.map ι
  let B : Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := B₀.map ι
  let Cm : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Matrix.of (fun a l => ι (C l a))
  let G : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Cm * genU Ω r s
  let a : GenField Ω r := ι (x c₁ ^ m s)
  have ha : a ≠ 0 := by
    simpa [a] using pow_ne_zero (m s) hx0
  have hF : flagMat φ c s = a • (A * G) := by
    have h1 : (Matrix.of (fun j l => ι (φ s j (c s l))) : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
        = a • (A * Cm) := by
      ext j l
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, A, Cm, A₀, Matrix.map_apply, smul_eq_mul,
        Finset.mul_sum]

      rw [hC l, map_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_smul, smul_eq_mul, a, ← map_mul]
      congr 1
      field_simp
    rw [flagMat, h1, Matrix.smul_mul, Matrix.mul_assoc]
  have hBA' : B * A = 1 := by
    have := congrArg (fun M : Matrix (Fin (r s)) (Fin (r s)) Ω => M.map ι) hBA
    simpa [B, A, A₀, Matrix.map_mul] using this
  haveI : IsLocalRing (regAt ξ' p') := EigSplit.isLocalRing_regAt p'
  obtain ⟨P, hPreg, hP0, hPinv, hPflag⟩ := GlobalTheory.T.flag_basis_change_integral (GenField Ω r) (regAt ξ' p') (r s) (fun c i => G i c) (fun k =>
    GlobalTheory.T.minor_ratio_regular_of_invertible (GenField Ω r) (regAt ξ' p') (n s) (r s) A B G a k (J ⟨s, k⟩)
      (fun j l => hreg _ (hAreg j l)) (fun l j => hreg _ (hBreg l j)) hBA' ha
      (by have := (hmin ⟨s, k⟩).1; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this)
      (by have := (hmin ⟨s, k⟩).2; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this))
  have hext := isExtOver_mk Ω (GenField Ω r) E
  let β : Fin (r s) → TensorProduct Ω (GenField Ω r) E := fun a => TensorProduct.mk Ω (GenField Ω r) E 1 (β₀ a)
  let T : (Fin (r s) → GenField Ω r) →ₗ[GenField Ω r] TensorProduct Ω (GenField Ω r) E :=
    Fintype.linearCombination (GenField Ω r) β
  have hTapp : ∀ v, T v = ∑ a, v a • β a := fun v => by simp [T, Fintype.linearCombination_apply]
  have hmap : ∀ (w : Fin (r s) → Fin (r s) → GenField Ω r) (i : ℕ),
      flagStep (GenField Ω r) (fun k => T (w k)) i = (flagStep (GenField Ω r) w i).map T := by
    intro w i
    simp only [flagStep, Submodule.map_span, Set.image_image]
  have hgenB : genB c s = fun k => T (fun a => G a k) := by
    funext k
    rw [hTapp]
    simp only [genB, G, Matrix.mul_apply, Cm, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_

    rw [hC l, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : TensorProduct.mk Ω (GenField Ω r) E 1 (C l b • β₀ b) = ι (C l b) • β b := hext.1 (C l b) (β₀ b)
    rw [h1, smul_smul, mul_comm]
  have hPfun : (fun k => ∑ a, P a k • β a) = fun k => T (fun a => P a k) := by
    funext k
    rw [hTapp]
  obtain ⟨U₁, hU₁, hq₁⟩ := EigSplit.exists_open_forall_mem_regAt p'
    (fun ab : Fin (r s) × Fin (r s) => P ab.1 ab.2) (fun ab => hPreg _ _)
  have hdetreg : P.det ∈ regAt ξ' p' := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hPreg _ _)
  obtain ⟨U₂, hU₂, hq₂⟩ := (regAt_unitAt_open X' _ ξ' p' P.det).2 ⟨hP0, hdetreg, hPinv⟩
  refine ⟨(f ⁻¹ᵁ U) ⊓ U₁ ⊓ U₂, ⟨⟨hU, hU₁⟩, hU₂⟩, fun k => ∑ a, P a k • β a, ?_, ?_⟩
  · intro i
    rw [hgenB, hPfun, hmap, hmap, hPflag]
  · rintro q - ⟨⟨hqU, hq1⟩, hq2⟩
    obtain ⟨hqf, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd q
    have hfq := hfr ⟨f q.1, hqf⟩ trivial hqU
    have hpull := FlagPull.pull_isFrameAt hd hext q hqf hfq
    exact GlobalTheory.T.frame_change_by_unit_matrix X' _ ξ' _ _ _ β q P hpull (fun a b => hq₁ q hq1 (a, b)) (hq₂ q hq2)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Flags
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.frame_matrices_regular_generic : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

theorem exists_extension_to_field {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩

theorem conj_eq_neg_of_sq_eq_neg_natCast {x : ℂ} {d : ℕ} (h : x ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ x = -x := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : x.re = 0 := by
    by_contra hne
    have : x.im = 0 := by
      have : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_pos.2 hne]
  apply Complex.ext <;> simp [h0]

theorem goodPt_or_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let r : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have hr : z ≫ 𝔐.f ≫ Y.s = spMap r := by
    simp [r, spMap]
  obtain ⟨τ, hτ⟩ := exists_extension_to_field r
  have h1 := congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
  have h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl ⟨τ, by rw [hr, hτ], h⟩
  · refine Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩
    · rw [Category.assoc, hr, ← hτ]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, RingHom.comp_apply, h, map_neg,
        conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum

variable {L : Type} [Field L] [NumberField L]

theorem finsum_log_add_sum_log {x : L} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace L, Real.log (v x) + ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = 0 := by
  have hmul : (Function.mulSupport fun v : FinitePlace L => v x).Finite :=
    FinitePlace.hasFiniteMulSupport hx
  have h1 : ∑ᶠ v : FinitePlace L, Real.log (v x) = Real.log (∏ᶠ v : FinitePlace L, v x) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun v _ => (FinitePlace.pos_iff.2 hx).ne')]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp [h1]
  have h2 : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    classical
    rw [← Real.log_prod fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx), ← norm_prod]
    have h3 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h4 : ∏ σ : L →+* ℂ, σ x = ∏ σ : L →ₐ[ℚ] ℂ, σ x :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun σ => (DFunLike.congr rfl rfl)
    rw [h4, ← h3, eq_ratCast, Complex.norm_ratCast]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hx]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem support_log_finite {x : L} (hx : x ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (v x)).Finite := by
  refine (show (Function.mulSupport fun v : FinitePlace L => v x).Finite from
    FinitePlace.hasFiniteMulSupport hx).subset fun v hv h => hv ?_
  simp [show v x = 1 from h]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def badPlaces (w : (Σ k, J k) → L) : Set (FinitePlace L) :=
  ⋃ p : Σ k, J k, {v | w p ≠ 0 ∧ v (w p) ≠ 1}

theorem badPlaces_finite (w : (Σ k, J k) → L) : (badPlaces w).Finite := by
  refine Set.finite_iUnion fun p => ?_
  by_cases hp : w p = 0
  · exact Set.finite_empty.subset fun v hv => hv.1 hp
  · refine (show (Function.mulSupport fun v : FinitePlace L => v (w p)).Finite from
      FinitePlace.hasFiniteMulSupport hp).subset fun v hv => hv.2

theorem eq_one_of_notMem {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w)
    {p : Σ k, J k} (hp : w p ≠ 0) : v (w p) = 1 := by
  by_contra h
  exact hv (Set.mem_iUnion.2 ⟨p, hp, h⟩)

theorem le_iSup_place (w : (Σ k, J k) → L) (v : FinitePlace L) (k : K) (c : J k) :
    v (w ⟨k, c⟩) ≤ ⨆ i, v (w ⟨k, i⟩) :=
  le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove c

theorem iSup_place_pos {w : (Σ k, J k) → L} (v : FinitePlace L) {k : K} (h : ∃ c, w ⟨k, c⟩ ≠ 0) :
    0 < ⨆ i, v (w ⟨k, i⟩) := by
  obtain ⟨c, hc⟩ := h
  exact (FinitePlace.pos_iff.2 hc).trans_le (le_iSup_place w v k c)

theorem iSup_place_eq_one {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w) {k : K}
    (h : ∃ c, w ⟨k, c⟩ ≠ 0) : ⨆ i, v (w ⟨k, i⟩) = 1 := by
  obtain ⟨c, hc⟩ := h
  haveI : Nonempty (J k) := ⟨c⟩
  refine le_antisymm (ciSup_le fun i => ?_) ?_
  · by_cases hi : w ⟨k, i⟩ = 0
    · rw [hi, map_zero]; exact zero_le_one
    · exact (eq_one_of_notMem hv hi).le
  · rw [← eq_one_of_notMem hv hc]
    exact le_iSup_place w v k c

theorem log_locRatio (a : K → ℤ) {w : (Σ k, J k) → L} (c₀ : (k : K) → J k)
    (h : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) (v : FinitePlace L) :
    Real.log (locRatio a w c₀ v) =
      (∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) -
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) := by
  unfold locRatio
  rw [Real.log_prod fun k _ => zpow_ne_zero _
    (div_ne_zero (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne'),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.log_zpow, Real.log_div (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne',
    mul_sub]

theorem ratio_sum (L : Type) [Field L] [NumberField L] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (a : K → ℤ) (w : (Σ k, J k) → L) (c₀ : (k : K) → J k) (u : L) :
    (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → u ≠ 0 →
    (∀ v, 0 < locRatio a w c₀ v) ∧ (Function.mulSupport (locRatio a w c₀)).Finite ∧
    ∑ᶠ v : FinitePlace L, (Real.log (locRatio a w c₀ v) - Real.log (v u)) =
      (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ u‖ + ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖) := by
  intro h h₀ hu
  refine ⟨fun v => ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => zpow_pos
      (div_pos (iSup_place_pos v (h k)) (FinitePlace.pos_iff.2 (h₀ k))) _
  · refine (badPlaces_finite w).subset fun v hv => ?_
    by_contra hb
    apply hv
    unfold locRatio
    refine Finset.prod_eq_one fun k _ => ?_
    rw [iSup_place_eq_one hb (h k), eq_one_of_notMem hb (h₀ k)]
    simp
  · have hS : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))).Finite := by
      refine (badPlaces_finite w).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [iSup_place_eq_one hb (h k), Real.log_one, mul_zero]
    have hT1 : ∀ k, (Function.support fun v : FinitePlace L =>
        (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := fun k =>
      (support_log_finite (h₀ k)).subset fun v hv hz => hv (by simp [show Real.log (v (w ⟨k, c₀ k⟩)) = 0 from hz])
    have hT : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := by
      refine (Set.finite_iUnion hT1).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      by_contra hk
      exact hb (Set.mem_iUnion.2 ⟨k, hk⟩)
    have hTsum : ∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) =
        -∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [finsum_sum_comm _ _ fun k _ => hT1 k, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_finsum,
        eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log (h₀ k)), mul_neg]
    have hu' := eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log hu)
    simp_rw [log_locRatio a c₀ h h₀]
    have hST := (hS.union hT).subset (Function.support_sub
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)))
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))))
    have hcomm : ∑ σ : L →+* ℂ, ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ =
        ∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    rw [finsum_sub_distrib hST (support_log_finite hu), finsum_sub_distrib hS hT, hTsum, hu',
      Finset.sum_add_distrib, hcomm]
    ring

end GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
end
