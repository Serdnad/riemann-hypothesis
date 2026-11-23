module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle311
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle298
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityLieAlgebraOfOmegaDensity
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle312
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqAmplitudeDoubleCosetInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.VolInvariant

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem eq_or_conj {E : Type} [Field E] [CharZero E] [StarRing E] (φ ψ : E →+* ℂ)
    (hψ : ∀ a, ψ (star a) = starRingEnd ℂ (ψ a)) (h : ∀ a, star a = a → φ a = ψ a) :
    φ = ψ ∨ φ = (starRingEnd ℂ).comp ψ := by
  by_cases hall : ∀ a : E, star a = a
  · left; ext a; exact h a (hall a)
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  set θ := b - star b with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hb.symm
  have hs : star θ = -θ := by simp [hθ]
  have hsq : φ θ ^ 2 = ψ θ ^ 2 := by
    rw [← map_pow, ← map_pow]; apply h; rw [star_pow, hs]; ring
  have h2 : star (2 : E) = 2 := star_ofNat 2
  have dec : ∀ a : E, ∃ u w : E, star u = u ∧ star w = w ∧ a = u + θ * w := by
    intro a
    refine ⟨(a + star a) / 2, (a - star a) / (2 * θ), ?_, ?_, ?_⟩
    · rw [star_div₀, star_add, star_star, h2, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', h2, hs]; field_simp; ring
    · field_simp; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
  · left; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    simp only [map_add (f := _), map_mul, h u hu, h w hw, h1]
  · right; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    rw [RingHom.comp_apply, ← hψ, star_add, star_mul', hu, hw, hs]
    simp only [map_add (f := _), map_mul, map_neg, h u hu, h w hw, h1]

theorem hasSignature_all (I : AutInst) {p q : ℕ} (h : HasSig I p q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) p q := by
  set v : InfinitePlace I.F := InfinitePlace.mk (φ.comp (algebraMap I.F I.E)) with hv
  have hc := I.cm.cmUnram.2.1
  have hag : ∀ a, star a = a → φ a = I.φ v a := by
    intro a ha
    obtain ⟨c, rfl⟩ := (I.cm.fixed a).1 ha
    rw [I.φ_over]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h1 | h1
    · rw [hv, h1]; rfl
    · rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, ha]
  rw [← (h v).1, ← (h v).2]
  rcases eq_or_conj φ (I.φ v) (hc _) hag with h1 | h1
  · have e0 : I.J.map φ = I.J.map (I.φ v) := congrArg (fun ψ : I.E →+* ℂ => I.J.map ψ) h1
    rw [e0]
    exact GlobalTheory.AutInhab.hasSignature_inst I v
  · refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ?_ ?_
    · exact (I.P_unit v).map (starRingEnd ℂ).mapMatrix
    · have := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
      simp only [Matrix.map_mul] at this
      have e1 : I.J.map φ = (I.J.map (I.φ v)).map (starRingEnd ℂ) := by
        ext i j; conv_lhs => rw [h1]
        rfl
      have e2 : ((I.P v).map (starRingEnd ℂ))ᴴ = ((I.P v)ᴴ).map (starRingEnd ℂ) := by
        ext i j; rfl
      rw [e1, e2, this]
      ext i j
      simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp

section Transport

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E'] {n : ℕ}

theorem exists_image (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin n) (Fin n) E') (A : GL (Fin n) E)
    (hA : (A : Matrix (Fin n) (Fin n) E)ᴴ * J * (A : Matrix (Fin n) (Fin n) E) = J'.map e)
    (L : Submodule (𝓞 E') (Fin n → E')) (hL : Submodule.IsLattice E' L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n → E', y ∈ L ↔ (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) ∈ Λ := by
  let σ : 𝓞 E' →+* 𝓞 E := (RingOfIntegers.mapRingEquiv e : 𝓞 E' ≃+* 𝓞 E)
  haveI : RingHomSurjective σ := ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩
  haveI : RingHomSurjective (e : E' →+* E) := ⟨e.surjective⟩
  let g : (Fin n → E') →ₛₗ[(e : E' →+* E)] (Fin n → E) :=
    { toFun := fun y => (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i))
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; ext i; simp
      map_smul' := fun c x => by
        rw [← Matrix.mulVec_smul]; congr 1; ext i; simp }
  let f : (Fin n → E') →ₛₗ[σ] (Fin n → E) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun c x => g.map_smulₛₗ (c : E') x }
  have hf : ∀ y, f y = (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z) hxy
    simp only [hf, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    ext i; exact e.injective (congrFun this i)
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => e.symm ((((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) i), ?_⟩
    simp only [hf, RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hform : ∀ x y, star (f y) ⬝ᵥ (J *ᵥ f x) = e (star y ⬝ᵥ (J' *ᵥ x)) := by
    intro x y
    rw [hf, hf, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    simp [dotProduct, Matrix.mulVec, he]
  have hint : ∀ a : E', e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
    intro a
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(RingOfIntegers.mapRingEquiv e).symm c, e.injective ?_⟩
      rw [← hc]
      exact e.apply_symm_apply _
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
  have hmem : ∀ y, y ∈ L ↔ f y ∈ L.map f := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, h⟩ => hinj h ▸ hz⟩
  refine ⟨L.map f, Submodule.IsLattice.of_fg E (hL.fg.map f), ?_, hmem⟩
  · intro x
    obtain ⟨x, rfl⟩ := hsurj x
    rw [← hmem, hd]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      rw [hform, hint]; exact h y hy
    · intro h y hy
      rw [← hint, ← hform]; exact h _ ⟨y, hy, rfl⟩

theorem exists_isometry (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) {n' : ℕ}
    (hn : n' = n) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E')
    (hJ : Jᴴ = J) (hJ' : J'ᴴ = J') (hdet : J.det ≠ 0) (hdet' : J'.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (L' : Submodule (𝓞 E') (Fin n' → E')) (hL' : Submodule.IsLattice E' L')
    (hd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range)
    {p q : ℕ} (hs : ∀ φ : E →+* ℂ, Formalism.UG.HasSignature (J.map φ) p q)
    (hs' : ∀ φ : E' →+* ℂ, Formalism.UG.HasSignature (J'.map φ) p q) :
    ∃ (A : Matrix (Fin n) (Fin n') E) (Λ : Submodule (𝓞 E) (Fin n → E)), Aᴴ * J * A = J'.map e ∧
      Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n' → E', y ∈ L' ↔ A *ᵥ (fun i => e (y i)) ∈ Λ := by
  subst hn
  obtain ⟨Λ₁, h1, h2, -⟩ := exists_image e he (J'.map e) J' 1 (by simp) L' hL' hd'
  have hh : (J'.map e)ᴴ = J'.map e := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← he, ← Matrix.conjTranspose_apply, hJ']
  have hde : (J'.map e).det ≠ 0 := by
    have := RingHom.map_det (e : E' →+* E) J'
    rw [RingHom.mapMatrix_apply] at this
    have h3 : (J'.map e).det = e J'.det := this.symm
    rw [h3]
    exact (map_ne_zero e).2 hdet'
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric E hE _ J (J'.map e) hJ hh hdet hde ⟨L, hL, hd⟩ ⟨Λ₁, h1, h2⟩
    fun φ => ⟨p, q, hs φ, hs' (φ.comp (e : E' →+* E))⟩
  obtain ⟨Λ, h3, h4, h5⟩ := exists_image e he J J' γ hγ L' hL' hd'
  exact ⟨γ, Λ, hγ, h3, h4, h5⟩

end Transport

theorem rank_eq (I : AutInst) {p q : ℕ} (h : HasSig I p q) : I.n = p + q := by
  obtain ⟨φ⟩ : Nonempty (I.E →+* ℂ) := inferInstance
  simpa using (Formalism.UG.P.sig_data _ p q (hasSignature_all I h φ)).1

theorem volumeInvariant : VolumeInvariant := by
  rintro I I' p q ⟨e, he⟩ h h' c μf _ _ c' μf' _ _ hc hc'
  have hn : I'.n = I.n := (rank_eq I' h').trans (rank_eq I h).symm
  obtain ⟨A, Λ, hA, hΛ, hd, hmem⟩ := exists_isometry I.cm.cmUnram e he hn I.J I'.J I.J_herm I'.J_herm
    I.J_det I'.J_det I.L (Submodule.IsLattice.of_fg I.E I.L_fg) (by simpa only [hform_eq] using I.L_dual)
    I'.L (Submodule.IsLattice.of_fg I'.E I'.L_fg) (by simpa only [hform_eq] using I'.L_dual)
    (hasSignature_all I h) (hasSignature_all I' h')
  obtain ⟨xf, hx⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ hΛ (by simpa only [hform_eq] using hd)
  exact GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus I I' e A xf he hn hA (hx ▸ hmem) c μf c' μf' hc hc'

end GlobalTheory.VolInvariant
end
end

section

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := rank_base_space D.R
  simp only [Ranks.N, zero_mul, add_zero] at this
  omega

variable {D : D7} (X : HidaSetting D)

def ci : Fin (2 * D.R.rS + D.R.k + 1) ≃ Fin X.B.I.n := finCongr (X.n_eq.trans (rank_eq D)).symm

def crdH (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E := fun i => X.bas.repr y (ci X i)

def vecOf : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).toLinearMap

def Jc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E :=
  fun i j => (VS D).hT (X.bas (ci X i)) (X.bas (ci X j))

def Lc : Submodule (𝓞 D.host.E) (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :=
  (VS D).L0.comap ((vecOf X).restrictScalars (𝓞 D.host.E))

def Pc (u : D.what₂.Word) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i b => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.eX a) i) b

def fc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin D.R.rS) D.host.E :=
  Matrix.of fun i a => crdH X (X.fY a) i

def Tc (u : D.what₂.Word) : D.host.F := (((D.mem u).A.T : ℕ) : D.host.F)

def tauOf (D : D7) (w : InfinitePlace D.host.E) : D.what₂.Tau :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose

def Direct (D : D7) (w : InfinitePlace D.host.E) : Prop := w.embedding = embS D (tauOf D w)

def A0 {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  (C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix id (ci X)

def Ac {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  if Direct D w then A0 X C w else (A0 X C w).map star

def sc (D : D7) (a : Fin D.R.rS) : ℝ := (2 * D.host.v) ^ (D.R.rS - (a : ℕ))

def trX {θ : ℝ} (C : Choice X θ) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then M else fun i j => star (M i j)

def Gm (D : D7) (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun w => cjw D w (y (tauOf D w))

end GlobalTheory.CovDom
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.hasDensityAtIdentityLieAlgebra_of_omegaDensity : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ (μ : Measure (Formalism.BasicNotions.UpqT P Q)) (c : ℝ≥0∞), μ.IsHaarMeasure → Formalism.BasicNotions.OmegaDensity μ c → PI.IsHaarOnM (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) ∧ HasDens (UH (Formalism.REAL.Jm ε)) (μ.map fun g => Matrix.of.symm (Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))) c := by
  first | exact @GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | exact GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity | (intros; apply GlobalTheory.OmegaFrobenius.hasDens_of_omegaDensity <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowPerpMass

theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  intro D u F0 he hz hp hs Λ hΛ
  let := D.host.cmStar
  obtain ⟨⟨hPD, hrk⟩, hL⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hInt, hdisc⟩ := hL Λ hΛ
  obtain ⟨hsym, hortho, hpos, -, -⟩ := GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties D.host.E D.sp.cm.cmUnram D.R.k
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  have hf : fDeg D.host.E = D.R.f := by
    have : NumberField.IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h2 := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
    have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 :=
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    have h4 : fDeg D.host.E = NumberField.InfinitePlace.nrRealPlaces D.host.E +
        NumberField.InfinitePlace.nrComplexPlaces D.host.E :=
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    show _ = 2 * D.R.ord
    omega
  have hmass := GlobalTheory.Mass.CyclicDisc.main GlobalTheory.T.maximalHermitianLattice_massRatio D.host.E (D.sp.X 0).V (D.sp.X 0).hT
    D.sp.cm.cmUnram (D.sp.X 0).herm hPD (by rw [hrk]; exact hk) (Fin D.R.k → D.host.E)
    (Cnt.stdH D.host.E D.R.k) hsym (Cnt.stdLat D.host.E D.R.k) (by rw [hrk]; exact hortho)
    (Lat.Tu D u) hp hs _ hInt hdisc
  rw [hrk, hf] at hmass
  have hS : mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) = Cnt.massS D D.R.k := rfl
  rw [hS] at hmass
  refine ⟨hmass, ?_⟩
  rw [hmass]

  have hT2 : (2 : ℝ) ≤ (Lat.Tu D u : ℝ) := by exact_mod_cast hp.two_le
  have hgeom : (Lat.Tu D u : ℝ) ^ (D.R.k - 1) ≤ ((Lat.Tu D u : ℝ) ^ D.R.k - 1) / ((Lat.Tu D u : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (Lat.Tu D u : ℝ) ^ D.R.k = (Lat.Tu D u : ℝ) * (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℝ) ≤ (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := one_le_pow₀ (by linarith)
    rw [e]; nlinarith
  have hNT : Cnt.NT D u ^ (D.R.k - 1) = ((Lat.Tu D u : ℝ) ^ (D.R.k - 1)) ^ D.R.f := by
    show (((D.mem u).A.T : ℝ) ^ D.R.f) ^ (D.R.k - 1) = _
    rw [← pow_mul, ← pow_mul, mul_comm]; rfl
  rw [hNT]
  have hm : 0 ≤ Cnt.massS D D.R.k := hpos.le
  gcongr

end GlobalTheory.Mass.RowPerpMass
end

section

open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix

theorem _root_.GlobalTheory.T.orbitalSquare_eq_hilbertSchmidt_normalisedVector : ∃ c₃ : ℝ, ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN A : ℝ) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), IsStdOf L μsec Bs → IsRatioN k r cN → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.IsBaseFrame Bs ν' m₀ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 F → ∀ γ : Point ℂ (r + 1), 0 < ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ → ThB.orbSq L F γ = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4 * (Real.pi ^ (rootPat γ).card) ^ 2 * ‖B.hsVec (D.vecV Bs ν' m₀ F (γ.1.map fun b => (b.2, b.1)))‖ ^ 2) := by
  first | exact @GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | exact GlobalTheory.ThA.OrbSq.orbSq_eq_vecV | (intros; apply GlobalTheory.ThA.OrbSq.orbSq_eq_vecV <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

theorem _root_.GlobalTheory.T.hsNormSq_amplitude_doubleCoset_invariant : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (A : LocS W), GoodW D τ w w' θ W → 0 < Tr D w → 0 < Tr D w' → IsSPsiEquiv W.z (psiS D W.z) W.π A.Φ → IsSPsiEquiv W.z' (psiS D W.z') W.π' A.Φ' → ContinuousOn A.Φ (UH (Hpk D.R.k D.R.rS)) → ContinuousOn A.Φ' (UH (Hpk D.R.k D.R.rS)) → ∀ (γ a a' : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (ν ν' : Measure (Mt D.R.k D.R.rS)), RelPt D W.z W.z' γ p → a ∈ Sset D.R.k D.R.rS W.z → a' ∈ Sset D.R.k D.R.rS W.z' → RMeas D W γ 1 ν → RMeas D W (a * γ * a'⁻¹) 1 ν' → hsNormSq (A.J ν' (a * γ * a'⁻¹)) = hsNormSq (A.J ν γ) := by
  first | exact @GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | exact GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset | (intros; apply GlobalTheory.AmpCoset.hsNormSq_amp_doubleCoset <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  first | exact @GlobalTheory.TenTypes.tensor_dict | exact GlobalTheory.TenTypes.tensor_dict | (intros; apply GlobalTheory.TenTypes.tensor_dict <;> assumption)
end
