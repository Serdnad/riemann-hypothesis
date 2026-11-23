module

public import Formalism.LocalRingCardinality.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle161
public import Mathlib.LinearAlgebra.Trace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle008
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.HermAdelicNorm

theorem congr_of_hasSignature {c p q : ℕ} {J J' : Matrix (Fin c) (Fin c) ℂ}
    (h : Formalism.UG.HasSignature J p q) (h' : Formalism.UG.HasSignature J' p q) :
    ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧ J' = Qᵀ * J * Q.map conj := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  set R : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P * P'⁻¹).val with hR
  have hRP : R * P'.val = P.val := by
    rw [hR, ← Units.val_mul, inv_mul_cancel_right]
  have h1 : Formalism.UG.cT (starRingEnd ℂ) R * J.reindex e e * R = J'.reindex e' e' := by
    have hu : IsUnit (Formalism.UG.cT (starRingEnd ℂ) (P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Formalism.UG.cT, Matrix.det_transpose,
        show ((P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det = _ from
          (RingHom.map_det (starRingEnd ℂ) _).symm]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 P'.isUnit).map _
    refine hu.mul_left_cancel (P'.isUnit.mul_right_cancel ?_)
    rw [hP', ← hP, ← hRP, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  let S : Matrix (Fin c) (Fin c) ℂ := R.submatrix e e'
  have hS : S.det ≠ 0 := by
    have : S * (P * P'⁻¹)⁻¹.val.submatrix e' e = 1 := by
      rw [Matrix.submatrix_mul_equiv, hR, Units.mul_inv, Matrix.submatrix_one_equiv]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  refine ⟨S.map conj, ?_, ?_⟩
  · rw [show (S.map conj).det = _ from (RingHom.map_det (starRingEnd ℂ) _).symm]
    exact (map_ne_zero _).2 hS
  · have h2 : (S.map conj).map conj = S := by
      ext a b
      simp
    have h3 : J' = (J'.reindex e' e').submatrix e' e' := by simp
    have h4 : J = (J.reindex e e).submatrix e e := by simp
    rw [h2, h3, ← h1]
    conv_rhs => rw [h4]
    rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e]
    rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_coord (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have h2 : star (2 : E) = 2 := star_ofNat 2
  obtain ⟨a, ha⟩ := (cm.fixed ((x + star x) / 2)).1 (by
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨b, hb⟩ := (cm.fixed ((x - star x) / (2 * θ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', h2, hθ]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

theorem exists_sq_sub (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) {d a : F}
    (hd : algebraMap F E d = θ * θ) (R : Type) [CommRing R] [Algebra F R] (y : E ⊗[F] R)
    (hy : Formalism.UG.sigR cm.sig R y * y = Formalism.UG.inclE R (algebraMap F E a)) :
    ∃ u w : R, algebraMap F R a = u ^ 2 - algebraMap F R d * w ^ 2 := by
  obtain ⟨u, w, rfl⟩ : ∃ u w : R, y = (1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w := by
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul x r =>
      obtain ⟨s, t, rfl⟩ := exists_coord cm h0 hθ x
      refine ⟨s • r, t • r, ?_⟩
      rw [TensorProduct.add_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨u, w, rfl⟩ := hx
      obtain ⟨u', w', rfl⟩ := hy
      exact ⟨u + u', w + w', by simp only [TensorProduct.tmul_add]; ring⟩
  refine ⟨u, w, Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := R)
    (algebraMap F E).injective ?_⟩
  have h1 : Formalism.UG.sigR cm.sig R ((1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w) =
      (1 : E) ⊗ₜ[F] u - θ ⊗ₜ[F] w := by
    rw [map_add (f := _)]
    change (star (1 : E)) ⊗ₜ[F] u + (star θ) ⊗ₜ[F] w = _
    rw [star_one, hθ, TensorProduct.neg_tmul, sub_eq_add_neg]
  have h2 : ∀ s : F, ∀ r : R, (algebraMap F E s) ⊗ₜ[F] r = (1 : E) ⊗ₜ[F] (algebraMap F R s * r) := by
    intro s r
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have h3 : Formalism.UG.inclE (F := F) R (algebraMap F E a) = (1 : E) ⊗ₜ[F] (algebraMap F R a) := by
    rw [← mul_one (algebraMap F R a), ← h2]
    rfl
  rw [h1, h3] at hy
  simp only [Algebra.TensorProduct.includeRight_apply]
  rw [← hy, TensorProduct.tmul_sub, ← h2, hd, pow_two, pow_two,
    ← Algebra.TensorProduct.tmul_mul_tmul]
  rw [show ((1 : E) ⊗ₜ[F] (u * u) : E ⊗[F] R) = (1 : E) ⊗ₜ[F] u * (1 : E) ⊗ₜ[F] u by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
  ring

theorem congr_of_signature_of_adelic_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (c : ℕ) (G G' : Matrix (Fin c) (Fin c) E), Gᴴ = G → G'ᴴ = G' → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) → (∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F) (G.det / G'.det)) → ∃ P : Matrix (Fin c) (Fin c) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  intro F E _ _ _ _ _ _ cm c G G' hG hG' hd hd' hs ⟨y, hy⟩
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (cm.cmUnram.2.1 τ x).symm)
  have hH : ∀ {M : Matrix (Fin c) (Fin c) E}, Mᴴ = M →
      ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (M a b) = M b a := fun h a b => by
    rw [hcc]
    exact congrFun (congrFun h b) a
  have hs' : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj := fun τ => by
    obtain ⟨p, q, h, h'⟩ := hs τ
    exact congr_of_hasSignature h h'
  obtain ⟨a, ha⟩ := (cm.fixed (G.det / G'.det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hG'])
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg (E := E)
  rw [hcc] at hθ
  obtain ⟨d, hdθ⟩ := (cm.fixed (θ * θ)).1 (by rw [star_mul', hθ]; ring)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h, map_zero])
  have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (by rw [← ha, h, map_zero])
  obtain ⟨u, w, huw⟩ := exists_sq_sub cm h0 hθ hdθ _ y (hy.trans (by rw [ha]))
  obtain ⟨s, t, hst⟩ := GlobalTheory.QNorm.hasseNormSt F d a hd0 ha0
    (fun ρ => by
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
      have h1 : τ (algebraMap F E a) = (Complex.ofRealHom.comp ρ) a :=
        ComplexEmbedding.lift_algebraMap_apply E _ a
      have h2 : 0 < (τ (G.det / G'.det)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hs' τ)
      rw [← ha, h1] at h2
      exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
    (fun v => by
      let ev : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) v
      have h1 := congrArg ev huw
      rw [map_sub, map_mul, map_pow, map_pow] at h1
      exact ⟨ev u, ev w, h1⟩)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E c G G'
    (hH hG) (hH hG') hd hd' hs' ⟨algebraMap F E s + algebraMap F E t * θ, by
      have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z :=
        fun z => (cm.fixed _).2 ⟨z, rfl⟩
      rw [hcc, star_add, star_mul', hf, hf, hθ, ← ha, hst, map_sub, map_mul, map_pow, map_pow, hdθ]
      ring⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [hPG]
    congr 2
    ext a b
    simp [hcc]

end GlobalTheory.HermAdelicNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree

theorem isOfFinOrder_of_conjIn_mem_St :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), IsDefUnimod hc J Λ → IsFrame β Λ → ∀ (u : UR hc J) (x : UA hc J), conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ St β → IsOfFinOrder u := by
  intro F E _ _ _ _ _ _ hc n J L β hU hβ u x hu
  open Matrix in
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    classical
    by_contra hspan
    have hproper : Submodule.span E (L : Set (Fin n → E)) < ⊤ := lt_top_iff_ne_top.mpr hspan
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
    let σ : E →+* E := hc.sig
    let z : Fin n → E := J⁻¹ *ᵥ (fun i => σ (f (Pi.single i 1)))
    have hpair (x : Fin n → E) : Formalism.UG.hform σ J x z = σ (f x) := by
      rw [Formalism.UG.P.hform_eq_dot, show J *ᵥ z = (fun i => σ (f (Pi.single i 1))) by
        simp only [z, mulVec_mulVec, J.mul_nonsing_inv hU.unit, one_mulVec], dotProduct]
      have hx : ∑ i, x i • Pi.single i (1 : E) = x := by
        simpa only [← Pi.single_smul', smul_eq_mul, mul_one] using
          LinearMap.sum_single_apply (fun _ : Fin n => E) x
      conv_rhs => rw [← hx, map_sum, map_sum]
      simp only [Function.comp_apply, LinearMap.map_smul, smul_eq_mul, map_mul]
    have hz : z ≠ 0 := by
      intro hz
      apply hf
      apply LinearMap.ext
      intro x
      apply σ.injective
      rw [LinearMap.zero_apply, map_zero, ← hpair, hz, Formalism.UG.P.csScale_hform_zero_right]
    have hann (x : Fin n → E) (hx : x ∈ L) : Formalism.UG.hform σ J x z = 0 := by
      have hfx : f x ∈ (Submodule.span E (L : Set (Fin n → E))).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span hx)
      rw [hmap, Submodule.mem_bot] at hfx
      rw [hpair, hfx, map_zero]
    have hzL : z ∈ L := by
      change z ∈ (L : Set (Fin n → E))
      rw [← hU.selfdual]
      intro x hx
      rw [hann x hx]
      exact (algebraMap (𝓞 E) E).range.zero_mem
    let v : InfinitePlace F := Classical.choice inferInstance
    let ι := v.embedding_of_isReal (hc.totReal.isReal v)
    rcases hU.tdef.2 ι with hpos | hneg
    · obtain ⟨a, ha, hsign⟩ := hpos z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
    · obtain ⟨a, ha, hsign⟩ := hneg z hz
      rw [hann z hzL, ← map_zero (algebraMap F E)] at ha
      exact (lt_irrefl (0 : ℝ)) (by simpa [(algebraMap F E).injective ha] using hsign)
  have hfin := Formalism.UG.Final.AdelicStabFiniteL F E (Fin n) hc.sig J (cm_comp hc) hU.herm hU.unit hU.tdef L
    (Module.Finite.iff_fg.2 hU.lat.fg) hspan x
  have hb := base_level_eq_adelic_level F E hc n J L β hβ
  let H : Subgroup (UR hc J) :=
    (Formalism.UG.levelAfL hc.sig J L).comap (conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))
  have hH : Finite H := by
    let f : H → Formalism.UG.stabAt (UQ hc J) ((Formalism.UG.levelAfL hc.sig J L).subgroupOf (UA hc J)) x :=
      fun γ => ⟨ratEl γ.1, (ratEl_mem_stabAt x γ.1).2 γ.2⟩
    refine Finite.of_injective f ?_
    intro a b hab
    exact Subtype.ext (ratEl_injective (congrArg Subtype.val hab))
  have huH : u ∈ H := by
    show conjIn hc J (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) u ∈ Formalism.UG.levelAfL hc.sig J L
    rw [← hb]
    refine ⟨?_, hu⟩
    rw [conjIn_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) (ratEl u).1.2) x.2
  have := isOfFinOrder_of_finite (⟨u, huH⟩ : H)
  exact H.subtype.isOfFinOrder this

end GlobalTheory.DefFree
end

section

noncomputable section

open Module

namespace GlobalTheory.QPosCompare

section Rat

variable {K X E : Type} [Field K] [AddCommGroup X] [Module K X] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} (j : X →ₛₗ[σ] E)

structure IsForm : Prop where
  basis : ∃ (n : ℕ) (b : Basis (Fin n) K X), LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range j) = ⊤
  inner : ∀ x y, ∃ a : K, inner ℂ (j x) (j y) = σ a

variable {j}

theorem IsForm.linInd (h : IsForm j) {ι : Type} [Fintype ι] {v : ι → X} (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun i => j (v i) := by
  obtain ⟨n, b, hb, -⟩ := h.basis
  let _ := σ.toAlgebra
  have h1 : LinearIndependent K fun i => b.equivFun (v i) :=
    hv.map' (b.equivFun : X →ₗ[K] (Fin n → K)) b.equivFun.ker
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun i => j (b i))
    (LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hb c
      (by simpa [Fintype.linearCombination_apply] using hc)))
  suffices he : (fun i => j (v i)) = (Fintype.linearCombination ℂ fun i => j (b i)) ∘
      fun i => (algebraMap K ℂ) ∘ b.equivFun (v i) by rw [he]; exact h3
  funext i
  simp only [Function.comp, Fintype.linearCombination_apply]
  conv_lhs => rw [← b.sum_equivFun (v i)]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]; rfl

end Rat

section Twist

open Formalism.IndefR.Links

variable {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] (s : Bool)

theorem tw_map_sub (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem tw_span (S : Set E) : Submodule.span ℂ (Tw.mk s '' S) = Tw.sub s (Submodule.span ℂ S) := by
  rw [← tw_map_sub, Submodule.map_span]; rfl

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ}
  (h : ∀ a, σ' a = cj s (σ a)) (j : X →ₛₗ[σ] E) (f : E →ₗ[ℂ] E')

end Twist

theorem isForm_of_pres {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* G} {S : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Formalism.IndefR.Bridge.ClassPres ι S σ ρ J χ) (M : Formalism.IndefR.Links.HMod (G → W))
    (hM : M.Is (Formalism.IndefR.Bridge.AdForms ι ρ J χ) (Formalism.IndefR.Bridge.adInner ι J P.y))
    (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) : IsForm j := by
  obtain ⟨hinj, hr, hip⟩ := hM
  obtain ⟨-, ⟨hli, hsp⟩, hiso⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨⟨_, S.basis, ?_, ?_⟩, fun x y => ⟨S.csum x y, ?_⟩⟩
  · refine LinearIndependent.of_comp M.e ?_
    have : (M.e ∘ fun i => j (S.basis i)) = fun i => P.extL (S.basis i) := funext fun i => hj _
    rw [this]; exact hli
  · apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_span, Submodule.map_top, hr, ← Set.range_comp]
    have : (M.e ∘ j) = P.extL := funext hj
    rw [this]; exact hsp
  · rw [hip, hj, hj]; exact hiso x y

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem lPos_iff_ne_bot : R.LPos F ↔ ∀ b, (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ :=
  forall_congr' fun b => pos_iff_ne_bot R F b


variable {R} in
theorem isForm_jX (h : R.IsModels) (t : T) : IsForm (R.jX t) :=
  isForm_of_pres (R.B.R t).pres (R.HX t) (h.HX t) (R.jX t) (h.jX t)

end Compare

end GlobalTheory.QPosCompare

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult MeasureTheory NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → (∀ P, R.EEat P ≤ R.EEat R.triv) ∧ (∀ P, R.EEat P ≤ LinearMap.range R.HE.e) ∧ ∀ P, ∀ S ∈ R.EEat P, ∀ S' ∈ R.EEat P, IsMultIP (R.MY 0) R.ν0 R.fd0 S S' (ipM (R.MY 0) R.ν0 R.fd0 S S') := by
  first | exact @GlobalTheory.GoodRowsLevel.eeat_sub_principal | exact GlobalTheory.GoodRowsLevel.eeat_sub_principal | (intros; apply GlobalTheory.GoodRowsLevel.eeat_sub_principal <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.piTensorProduct_map_surjective_and_dual_vanishes : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : ι → Type) [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)] (π : ∀ τ, A τ →ₗ[ℂ] B τ), (∀ τ, Function.Surjective (π τ)) → Function.Surjective (PiTensorProduct.map π) ∧ ∀ l : Module.Dual ℂ (⨂[ℂ] τ, A τ), (∀ (τ : ι) (x : ∀ σ, A σ), π τ (x τ) = 0 → l (PiTensorProduct.tprod ℂ x) = 0) → ∀ z, PiTensorProduct.map π z = 0 → l z = 0 := by
  first | exact @GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker | exact GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker | (intros; apply GlobalTheory.TensorKernel.piTensor_map_surjective_and_ker <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.exists_piTensor_mvPolynomial_prod_equiv : ∀ (ι σ : Type) [Fintype ι], ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, ∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  first | exact @GlobalTheory.PolyTensor.exists_piTensor_equiv | exact GlobalTheory.PolyTensor.exists_piTensor_equiv | (intros; apply GlobalTheory.PolyTensor.exists_piTensor_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finrank_eq_card_mul_and_trace_eq_zero_of_free_values_alt : ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  first | exact @GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | exact GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values | (intros; apply GlobalTheory.finrank_eq_card_mul_and_trace_eq_zero_of_free_values <;> assumption)
end
