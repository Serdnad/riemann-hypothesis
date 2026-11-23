module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Matrix in
theorem negIndex_transpose_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : GlobalTheory.Inertia.negIndex Jᵀ = q ∧ J.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have hd : Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [← fromBlocks_diagonal, Formalism.UG.Jpq]
    congr 1
    rw [← diagonal_neg]
    rfl
  have hPd : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det ≠ 0 := P.det_ne_zero
  constructor
  · have ht := congrArg Matrix.transpose hP
    rw [hd, diagonal_transpose, transpose_mul, transpose_mul, Formalism.UG.cT, transpose_transpose,
      ← Matrix.mul_assoc] at ht
    have h1 := GlobalTheory.Inertia.negIndex_eq_card_of_congr_diagonal hPd ht
    have h2 : (J.reindex e e)ᵀ = Jᵀ.submatrix e.symm e.symm := rfl
    rw [h2, GlobalTheory.Inertia.negIndex_submatrix_equiv] at h1
    rw [h1, Finset.card_filter, Fintype.sum_sum_type]
    simp [not_lt.2 (zero_le_one' ℝ)]
  · intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_reindex_self, h0, hd, det_diagonal] at h1
    simp only [mul_zero, zero_mul] at h1
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h1.symm
    rcases k with k | k <;> simp

variable {D : D7}

theorem cc_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (a b : Fin r) :
    cc (gmW V hr a b) = gmW V hr b a := by
  subst hr
  show IsCMField.complexConj D.host.E (-(V.hT (V.frame b) (V.frame a))) = -(V.hT (V.frame a) (V.frame b))
  rw [map_neg]
  exact congrArg Neg.neg (LinearMap.isSymm_def.1 V.herm (V.frame b) (V.frame a))

theorem herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm) =
      -V.hT y x := by
  subst hr
  rw [Formalism.L2.Pj.DatLin.sesq_repr V.hT V.frame y x, Finset.sum_comm, herm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show V.frame.repr x a * (-(V.hT (V.frame b) (V.frame a))) * star (V.frame.repr y b) = _
  ring

theorem trace_herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    Algebra.trace ℚ D.host.E (D.host.xi0 *
      herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm)) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT x y) := by
  rw [herm_gmW, ← _root_.Formalism.L2.Pj.trace_cc D (D.host.xi0 * V.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt]
  have h : IsCMField.complexConj D.host.E (V.hT x y) = V.hT y x := LinearMap.isSymm_def.1 V.herm x y
  rw [h, mul_neg, neg_mul]

theorem posIndex_gmW (V : HSp D) (hV : V.SigOK) {r : ℕ} (hr : V.rank = r) (τ : D.host.E →+* ℂ) :
    GlobalTheory.Inertia.posIndex ((gmW V hr).map τ) = (V.sig τ).2 ∧ (gmW V hr).det ≠ 0 := by
  subst hr
  obtain ⟨h1, h2⟩ := negIndex_transpose_of_hasSignature (hV τ)
  have e : gmW V rfl = -V.gram.transpose := rfl
  constructor
  · rw [← h1, ← GlobalTheory.Inertia.posIndex_neg, e]
    congr 1
    ext a b
    simp
  · rw [e, Matrix.det_neg, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) fun h0 => h2 ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.RecDict
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincFree

theorem cmType_of_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hE]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : z.re = 0 := by
      by_contra h
      have h4 : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [h4] at h1
      nlinarith [mul_self_nonneg z.re]
    apply Complex.ext <;> simp [h3]
  have hne : H.rt0 ≠ 0 := by
    intro h
    have h1 := H.sqrt_neg_disc_sq
    rw [h] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  rw [ComplexEmbedding.conjugate_coe_eq, hconj _ hsq]
  constructor
  · intro h h'
    rw [h] at h'
    exact hne (by linear_combination (-1 / 2 : ℂ) * h')
  · intro h
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [hsq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    {r : ℕ} (φ : L →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ LinearMap.range φ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ LinearMap.range φ) :
    ∃ g : L ≃ₗ[𝓞 E] L, ∀ a, φ (g a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)
  let g : L →ₗ[𝓞 E] L :=
    { toFun := f
      map_add' := fun a b => hφ (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), Matrix.mulVec_add])
      map_smul' := fun c a => hφ (by
        rw [RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩
  · have h : f a = f b := hab
    rw [← hli (φ a), ← hli (φ b), ← hf, ← hf, h]
  · obtain ⟨a, ha⟩ := (hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2
      (by rw [hri]; exact LinearMap.mem_range_self φ b)
    exact ⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩

theorem princ_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb
  obtain ⟨hU, hhalf, -⟩ := hγ
  obtain ⟨g, hg⟩ := exists_equiv_of_stab φ0 hinj γ hU.2
  have hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a' := by
    intro a a'
    have : ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ) := by
      rw [hEF, hEF, hg, hg, hU.1]
    exact_mod_cast this
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by
    obtain ⟨e, he⟩ := hhalf a ha
    exact ⟨e, hinj (by rw [hg, he, map_add (f := _), map_nsmul])⟩)
  have hfin := Di.fin
  refine GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ
    (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb
  · rw [hΨ, hΨ]; exact cmType_of_rt H τ
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ0
  · rw [LinearMap.coe_range]; exact hsp
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add (f := _), map_nsmul]⟩

end GlobalTheory.PrincFree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.framedPoints_glue_principal_cover : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X), x ≫ Xo.s = sOf c S → ∀ (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ y : ∀ i, FrPt Xo c (Localization.Away (h i)), (∀ i, (y i).x = spMap (algebraMap S (Localization.Away (h i))) ≫ x) → (∀ i j (α : Localization.Away (h i) →ₐ[c.F] Localization.Away (h i * h j)) (β : Localization.Away (h j) →ₐ[c.F] Localization.Away (h i * h j)), α.toRingHom.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.toRingHom.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ z, FrMap α (y i) z → FrMap β (y j) z) → ∃ y₀ : FrPt Xo c S, y₀.x = x ∧ ∀ i, FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (h i))) y₀ (y i) := by
  first | exact @GlobalTheory.Frames.frPt_glue | exact GlobalTheory.Frames.frPt_glue | (intros; apply GlobalTheory.Frames.frPt_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompRat.exists_coeff_idempotents_any_level | exact GlobalTheory.CompRat.exists_coeff_idempotents_any_level | (intros; apply GlobalTheory.CompRat.exists_coeff_idempotents_any_level <;> assumption)
end

section

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E) :
    FD.transvMat G ξ α *ᵥ x = x + (α * FD.herm G x ξ) • ξ := by
  funext a
  simp only [FD.transvMat, FD.herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem herm_add_smul_left (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G (x + c • ξ) y = FD.herm G x y + c * FD.herm G ξ y := by
  simp only [FD.herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_smul_right (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G x (y + c • ξ) = FD.herm G x y + FD.cc c * FD.herm G x ξ := by
  simp only [FD.herm, FD.cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_add (f := _),
    map_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (x y : Fin r → E) : FD.cc (FD.herm G x y) = FD.herm G y x := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG

  simp only [FD.herm, FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem transvMat_mul_neg (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : FD.transvMat G ξ α * FD.transvMat G ξ (-α) = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, hξ, mul_zero, add_zero, neg_mul,
    neg_smul, neg_add_cancel_right]

noncomputable def transv (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : GL (Fin r) E where
  val := FD.transvMat G ξ α
  inv := FD.transvMat G ξ (-α)
  val_inv := transvMat_mul_neg G hξ α
  inv_val := by simpa using transvMat_mul_neg G hξ (-α)

theorem herm_transvMat {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0) {α : E} (hα : FD.cc α = -α) (x y : Fin r → E) :
    FD.herm G (FD.transvMat G ξ α *ᵥ x) (FD.transvMat G ξ α *ᵥ y) = FD.herm G x y := by
  have e : FD.cc (α * FD.herm G y ξ) = -α * FD.herm G ξ y := by
    rw [← hα, ← cc_herm hG y ξ]
    exact map_mul (IsCMField.complexConj E) _ _
  rw [transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, herm_add_smul_right,
    herm_add_smul_right, hξ, e]
  ring

omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

theorem exists_data : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M m : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (ξ0 κ0 : E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Gm.det ≠ 0 → p0 ≤ r → (∀ τ ∈ Ψ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.cc ξ0 = -ξ0 → ξ0 ≠ 0 → (κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)) → (∀ τ ∈ Ψ, (τ κ0).im < 0) → 0 < m → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) / (M : E) * κ0 * FD.herm Gm x y)) → ∃ X : FD.Data E r, X.Ψ = Ψ ∧ X.Gm = Gm ∧ X.p0 = p0 ∧ X.Λ = Λ ∧ X.ξ0 = ξ0 ∧ X.κ0 = κ0 ∧ X.m = m ∧ (∀ γ, γ ∈ X.Γ ↔ FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∀ la γ, X.χ la γ = 1 := by
  intro hMink E _ _ _ r p0 M m Ψ Gm Λ ξ0 κ0 hΨ hG hdet hp hsig hfg hsp hM hξ hξ0 hκ hκs hm hint
  obtain ⟨Γ, hΓ, hidx⟩ :=
    GlobalTheory.CongruenceIndex.congruence_finiteIndex E r M Gm Λ hfg (by omega)
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hκ0 : κ0 ≠ 0 := by rcases hκ with h | h <;> simp [h, hξ0]
  have hξ' : IsCMField.complexConj E ξ0 = -ξ0 := hξ
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have halg : IsAlgebraic ℤ (((m : E) / (M : E) * κ0)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  refine ⟨{
    Ψ := Ψ, cmType := hΨ, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := p0, p0_le := hp
    signature := fun τ => hsig τ.1 τ.2
    Λ := Λ, Λ_fg := hfg, Λ_span := hsp
    den := (k : 𝓞 E), den_ne := Int.cast_ne_zero.2 hk
    Λ_int := fun x hx y hy => ?_
    Γ := Γ, Γ_stab := fun γ h => ((hΓ γ).1 h).1, Γ_index := hidx
    Γ_free := fun γ h => GlobalTheory.GamFree.gam_free hMink E r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM
      ((hΓ γ).1 h).1 ((hΓ γ).1 h).2
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one _).symm
    χ_add := fun _ _ _ _ => (mul_one _).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow _⟩
    ξ0 := ξ0, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := κ0, κ0_xi := hκ
    κ0_sign := fun τ => hκs τ.1 τ.2
    m := m, m_pos := hm
    transv := fun ξ hξΛ hiso s hs hsi => ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hΓ, fun _ _ => rfl⟩
  · have h := hki.mul (hint x hx y hy)
    have e : k • ((m : E) / (M : E) * κ0)⁻¹ * ((m : E) / (M : E) * κ0 * FD.herm Gm x y) =
        (((k : 𝓞 E) : 𝓞 E) : E) * FD.herm Gm x y := by
      rw [zsmul_eq_mul]
      simp only [map_intCast]
      field_simp
    rwa [e] at h
  · have hs' : IsCMField.complexConj E s = s := hs
    have hα : FD.cc ((m : E) * s * κ0) = -((m : E) * s * κ0) := by
      simp [FD.cc, hs', hκc]
    have hMi : IsIntegral ℤ (M : E) := isIntegral_natCast M
    have key : ∀ v ∈ Λ, (s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ ∈ Λ := fun v hv =>
      smul_mem_of_isIntegral Λ (hsi.mul (hint v hv ξ hξΛ)) hξΛ
    have e : ∀ v, ((m : E) * s * κ0 * FD.herm Gm v ξ) • ξ =
        M • ((s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ) := by
      intro v
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1
      field_simp
    refine ⟨transv Gm hiso ((m : E) * s * κ0), (hΓ _).2 ⟨⟨herm_transvMat hG hiso hα, fun x => ?_⟩,
      fun v hv => ⟨_, key v hv, ?_⟩⟩, rfl⟩
    · change x ∈ Λ ↔ FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ x ∈ Λ
      rw [transvMat_mulVec]
      refine ⟨fun hx => Λ.add_mem hx (by rw [e]; exact nsmul_mem (key x hx) M), fun hx => ?_⟩
      have h := nsmul_mem (key _ hx) M
      rw [← e, herm_add_smul_left, hiso, mul_zero, add_zero] at h
      simpa using Λ.sub_mem hx h
    · change FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ v = _
      rw [transvMat_mulVec, e]

end GlobalTheory.FlagData
end
