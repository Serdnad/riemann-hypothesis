module

public import GroundTheory.AutomorphicForms.AnisotropicUnitaryRes
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Bundle002
public import GroundTheory.AutomorphicForms.ReductionHeight
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import GroundTheory.GlobalFields.TateThesis.Conductor
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.AutomorphicForms.Bundle006
import GroundTheory.LocalFields.Bundle001
public import GroundTheory.LocalFields.Bundle007
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

section Algebraic

variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

local notation "𝒩" => Fintype.card (ι × κ)

theorem baseMap_eq_tensorMap (f : R →ₐ[K] R') :
    (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E) = tensorMap (E := E) f := rfl

variable {R}

theorem hermValue_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    baseMap f (hermValue K H R x) = hermValue K H R' (fun i => baseMap f (x i)) := by
  rw [baseMap_eq_tensorMap]
  unfold hermValue
  change (tensorMap (E := E) f : R ⊗[K] E →+* R' ⊗[K] E) (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  congr 1
  · funext i
    exact tensorMap_conjBase f (x i)
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a c
    change tensorMap E f (Algebra.TensorProduct.includeRight (H a c)) =
      Algebra.TensorProduct.includeRight (H a c)
    exact tensorMap_includeRight f (H a c)

variable (R)

def hermCoords (y : Fin 𝒩 → R) : κ → R := coords b R (hermValue K H R (ofResVec b R y))

theorem hermCoords_smul (t : R) (y : Fin 𝒩 → R) :
    hermCoords H b R (t • y) = t ^ 2 • hermCoords H b R y := by
  rw [hermCoords, ofResVec_smul, hermValue_smul, map_smul, sq]
  rfl

variable {R}

theorem ofResVec_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    ofResVec b R' (f ∘ y) = fun i => baseMap f (ofResVec b R y i) := by
  apply resVec_injective b R'
  rw [resVec_ofResVec, resVec_baseMap, resVec_ofResVec]

theorem hermCoords_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    hermCoords H b R' (f ∘ y) = f ∘ hermCoords H b R y := by
  rw [hermCoords, ofResVec_comp, ← hermValue_baseMap, coords_baseMap]
  rfl

def hermPoly (k : κ) : MvPolynomial (Fin 𝒩) K :=
  hermCoords H b (MvPolynomial (Fin 𝒩) K) MvPolynomial.X k

theorem aeval_hermPoly (y : Fin 𝒩 → R) (k : κ) :
    MvPolynomial.aeval y (hermPoly H b k) = hermCoords H b R y k := by
  have h := congrFun (hermCoords_comp H b (MvPolynomial.aeval y) MvPolynomial.X) k
  have hy : (MvPolynomial.aeval y : MvPolynomial (Fin 𝒩) K →ₐ[K] R) ∘ MvPolynomial.X = y := by
    funext p
    simp
  rw [hy] at h
  exact h.symm

def inside₂ (S : Type*) [CommRing S] : GL ι S →* GL ι S where
  toFun g := ⟨(↑g⁻¹ : Matrix ι ι S)ᵀ, (g : Matrix ι ι S)ᵀ,
    by rw [← transpose_mul, g.mul_inv, transpose_one],
    by rw [← transpose_mul, g.inv_mul, transpose_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' g h := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul]

theorem trHom_invTr (g : GL ι (R ⊗[K] E)) :
    (trHom b R (inside₂ (R ⊗[K] E) g) : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ↑g := by
  rw [trHom_val]
  congr 1

def diagGL (f : R →ₐ[K] R') : GL ι (R ⊗[K] E) →* GL ι (R' ⊗[K] E) :=
  Units.map ((AlgHom.mapMatrix (baseMap f) : Matrix ι ι (R ⊗[K] E) →ₐ[K] Matrix ι ι (R' ⊗[K] E)).toRingHom.toMonoidHom)

theorem diagGL_val (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    (diagGL f g : Matrix ι ι (R' ⊗[K] E)) = (g : Matrix ι ι (R ⊗[K] E)).map (baseMap f) := rfl

theorem invTr_diagGL (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    inside₂ (R' ⊗[K] E) (diagGL f g) = diagGL f (inside₂ (R ⊗[K] E) g) := by
  ext : 1
  simp only [diagGL_val]
  show ((↑(diagGL f g)⁻¹ : Matrix ι ι (R' ⊗[K] E)))ᵀ = ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ).map _
  rw [← map_inv, diagGL_val, transpose_map]

end Algebraic

section Heights

variable [NumberField K] {d : ℕ} (b : Basis (Fin d) K E)

local notation "𝒩'" => Fintype.card (ι × Fin d)

theorem hermCoords_vecMul_trHom (x : Fin 𝒩' → K) (u : unitaryPoints K E H 𝔸[K]) :
    hermCoords H b 𝔸[K] (Reduction.ratVec x ᵥ* (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)) :
      Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])) = Reduction.ratVec (hermCoords H b K x) := by
  have hx : Reduction.ratVec x = resVec b 𝔸[K]
      (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i)) := by
    rw [resVec_baseMap, resVec_ofResVec]
    rfl
  rw [hx, resVec_vecMul_trHom, hermCoords, ofResVec_resVec]
  have h := hermValue_mulVec (K := K) (H := H) (u⁻¹)
    (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i))
  rw [show unitaryMat (u⁻¹) = (↑(u : GL ι (𝔸[K] ⊗[K] E))⁻¹ : Matrix ι ι (𝔸[K] ⊗[K] E)) from rfl]
    at h
  rw [h, ← hermValue_baseMap, coords_baseMap]
  rfl

end Heights

end Anisotropic

end

end GroundTheory.Automorphic
end

section

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def detClassSubgroup (U : Subgroup (FiniteAdelicGL K n)) :
    Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔
    U.map (Matrix.GeneralLinearGroup.det : FiniteAdelicGL K n →* (FiniteAdeleRing (𝓞 K) K)ˣ)

variable {K n}

theorem det_diagonalGL {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL d) = ∏ k, d k := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagonalGL, det_diagonal, Units.coe_prod]

theorem det_diagonalGL_mulSingle {R : Type*} [CommRing R] (hn : 0 < n) (a : Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) a)) = a := by
  rw [det_diagonalGL, Finset.prod_pi_mulSingle', if_pos (Finset.mem_univ _)]

theorem exists_eq_finiteDiagonal_mul_mul (hn : 0 < n) {U : Subgroup (FiniteAdelicGL K n)}
    (hU : IsOpen (U : Set (FiniteAdelicGL K n))) {g g' : FiniteAdelicGL K n}
    (h : (Matrix.GeneralLinearGroup.det g)⁻¹ * Matrix.GeneralLinearGroup.det g' ∈
      detClassSubgroup K n U) :
    ∃ γ : GL (Fin n) K, ∃ u ∈ U, g' = finiteDiagonal K n γ * g * u := by
  obtain ⟨_, ⟨κ, rfl⟩, _, ⟨u₀, hu₀, rfl⟩, hκ⟩ := Subgroup.mem_sup.1 h
  set δ : GL (Fin n) K := diagonalGL (Pi.mulSingle (⟨0, hn⟩ : Fin n) κ)
  set g₁ : FiniteAdelicGL K n := finiteDiagonal K n δ * g * u₀
  have hg₁ : Matrix.GeneralLinearGroup.det g₁ = Matrix.GeneralLinearGroup.det g' := by
    simp only [g₁, map_mul, det_finiteDiagonal, δ, det_diagonalGL_mulSingle hn]
    rw [mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_assoc, hκ, mul_inv_cancel_left]
  set x : FiniteAdelicGL K n := g' * g₁⁻¹
  have hx : Matrix.GeneralLinearGroup.det x = 1 := by
    rw [map_mul, map_inv, ← hg₁, mul_inv_cancel]
  have hcont : Continuous fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁ :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul continuous_const
  have hx1 : g₁⁻¹ * x⁻¹ * x * g₁ = 1 := by group
  have hO : (fun h : FiniteAdelicGL K n => g₁⁻¹ * h⁻¹ * x * g₁) ⁻¹' (U : Set (FiniteAdelicGL K n)) ∈
      𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [hx1]; exact U.one_mem))
  obtain ⟨γ, -, hγ⟩ := exists_finiteDiagonal_mem_nhds K n hx hO
  refine ⟨γ * δ, u₀ * (g₁⁻¹ * (finiteDiagonal K n γ)⁻¹ * x * g₁), mul_mem hu₀ hγ, ?_⟩
  simp only [x, g₁, map_mul]
  group

open GroundTheory.Global GroundTheory.Global.IdeleGroup

variable (K)

theorem toFinite_diagonal (a : Kˣ) :
    toFinite K (IdeleGroup.diagonal K a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a :=
  Units.ext rfl

theorem comap_toFinite_sup (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L).comap (toFinite K) =
      (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨_, ⟨a, rfl⟩, l, hl, hal⟩ := Subgroup.mem_sup.1 (Subgroup.mem_comap.1 hx)
    refine Subgroup.mem_sup.2 ⟨IdeleGroup.diagonal K a, ⟨a, rfl⟩, (IdeleGroup.diagonal K a)⁻¹ * x,
      ?_, mul_inv_cancel_left _ _⟩
    rw [Subgroup.mem_comap, map_mul, map_inv, toFinite_diagonal, ← hal, inv_mul_cancel_left]
    exact hl
  · refine sup_le ?_ (Subgroup.comap_mono le_sup_right)
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_comap, toFinite_diagonal]
    exact Subgroup.mem_sup_left ⟨a, rfl⟩

def toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) :=
  (QuotientGroup.mk' _).comp (toFinite K)

theorem toFiniteQuotient_surjective (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    Function.Surjective (toFiniteQuotient K L) :=
  (QuotientGroup.mk'_surjective _).comp fun x => ⟨ofFinite x, toFinite_ofFinite x⟩

theorem ker_toFiniteQuotient (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (toFiniteQuotient K L).ker = (IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K) := by
  rw [toFiniteQuotient, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_toFinite_sup]

def finiteQuotientEquiv (L : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ L) ≃*
      IdeleGroup K ⧸ ((IdeleGroup.diagonal K).range ⊔ L.comap (toFinite K)) :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_toFiniteQuotient K L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toFiniteQuotient_surjective K L))).symm

def finiteQuotientEquivClassGroup :
    (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ ((FiniteAdeleRing.unitEmbedding (𝓞 K) K).range ⊔ finiteLevel 0) ≃*
      ClassGroup (𝓞 K) :=
  (finiteQuotientEquiv K (finiteLevel 0)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      congr 1
      ext x
      exact (mem_standardOpenSubgroup_iff_toFinite_mem x).symm)).trans
      IdeleGroup.quotientEquivClassGroup)

variable {K}

theorem det_mem_of_forall_mem {R : Type*} [CommRing R] (T : Subring R) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a b, M a b ∈ T) : M.det ∈ T := by
  have : M = T.subtype.mapMatrix (Matrix.of fun a b => (⟨M a b, hM a b⟩ : T)) := by
    ext a b
    rfl
  rw [this, ← RingHom.map_det]
  exact SetLike.coe_mem _

end AdelicGLn

end

end GroundTheory.Automorphic
end

section

noncomputable section

namespace GroundTheory.Automorphic

open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial

theorem mem_or_mul_inv_mem_of_natCard_eq_two {G : Type*} [CommGroup G] {N : Subgroup G}
    (hN : Nat.card (G ⧸ N) = 2) {t : G} (ht : t ∉ N) (u : G) : u ∈ N ∨ u * t⁻¹ ∈ N := by
  by_contra H
  push Not at H
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).1 hN
  have h1 : (QuotientGroup.mk t : G ⧸ N) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk u : G ⧸ N) ≠ 1 := by rw [Ne, QuotientGroup.eq_one_iff]; exact H.1
  have h3 := QuotientGroup.eq.1 ((hy _ h1).trans (hy _ h2).symm)
  apply H.2
  rwa [mul_comm]

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem mem_range_normUnits_iff (u : Fˣ) :
    u ∈ (normUnits F E).range ↔ ∃ z : E, Algebra.norm F z = u := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (coe_normUnits w).symm⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by rintro rfl; rw [Algebra.norm_zero] at hz; exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [coe_normUnits, Units.val_mk0, hz])⟩

end General

section Local

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]

theorem natCard_quotient_range_normUnits_eq_two :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by
  obtain ⟨_, _, _, _⟩ := exists_isNonarchimedeanLocalField_valuativeExtension F E
  rw [natCard_units_quotient_range_normUnits, Algebra.IsQuadraticExtension.finrank_eq_two]

namespace HermitianForm

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

end HermitianForm

end Local

end GroundTheory.Automorphic

end
end
