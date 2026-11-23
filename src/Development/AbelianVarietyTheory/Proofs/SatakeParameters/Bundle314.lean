module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle302
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle234
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrameLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by funext l; simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

theorem seamVec_apply {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (x : Sp X.E n) (l : Fin n) :
    seamVec s n x l = s.iE (x l) := rfl

theorem seamVec_injective {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : Function.Injective (seamVec s n) := by
  intro x y hxy
  funext l
  exact s.iE.injective (congrFun hxy l)

theorem seam_lat_eq_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat M = M.map (seamVec s n) := by
  unfold Seam.lat
  rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = seamVec s n '' M from rfl,
    ← Submodule.map_coe]
  exact Submodule.span_eq _

theorem localization_map_seamVec {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map (seamVec s n)) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map (seamVec s n) := by
  set ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE with hψ
  ext x
  constructor
  · rintro ⟨r, hr, z, hz, hzx⟩
    have hfy : seamVec s n (fun l => s.iE.symm (x l)) = x := by
      funext l
      simp [seamVec_apply]
    refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
    · intro hm
      apply hr
      have := (mem_seamP s P (ψ.symm r)).2 hm
      simpa [ψ] using this
    · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
        apply seamVec_injective s n
        rw [(seamVec s n).map_smulₛₗ, hfy, hzx]
        show ψ (ψ.symm r) • x = r • x
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact hz
  · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
    refine ⟨ψ r, ?_, r • y, hy, ?_⟩
    · intro hm
      exact hr ((mem_seamP s P r).1 hm)
    · rw [(seamVec s n).map_smulₛₗ]
      rfl

theorem stdLat_map_seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    (stdLat X.E n).map (seamVec s n) = stdLat D.host.E n := by
  ext y
  rw [Submodule.mem_map]
  unfold Formalism.L2.Col.stdLat
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hx l)
    refine (Submodule.mem_one).2 ⟨RingOfIntegers.mapRingEquiv s.iE r, ?_⟩
    rw [seamVec_apply, ← hr]
    rfl
  · intro hy
    refine ⟨fun l => s.iE.symm (y l), fun l => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hy l)
      refine (Submodule.mem_one).2 ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, ?_⟩
      show _ = s.iE.symm (y l)
      rw [← hr]
      rfl
    · funext l
      simp [seamVec_apply]

theorem mvL_seamGL_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    mvL (seamGL s g) (M.map (seamVec s n)) = (M.map (g.toLinearMap.restrictScalars (𝓞 X.E))).map (seamVec s n) := by
  unfold mvL
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    show seamVec s n (g x) = toLE (seamGL s g) (seamVec s n x)
    rw [toLE_apply]
    exact (seamGL_mulVec s g x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨seamVec s n x, ⟨x, hx, rfl⟩, ?_⟩
    show toLE (seamGL s g) (seamVec s n x) = seamVec s n (g x)
    rw [toLE_apply]
    exact seamGL_mulVec s g x

theorem seamGL_stdAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) →
    mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  intro D X s n P g N hg
  have hstd : (stdAt X.E n P).map (g.toLinearMap.restrictScalars (𝓞 X.E)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).2 hx
    · intro hy
      refine ⟨g.symm y, (hg _).1 (by simpa using hy), by simp⟩
  show mvL (seamGL s g) (Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (stdLat D.host.E n)) = _
  rw [← stdLat_map_seamVec s n, localization_map_seamVec, mvL_seamGL_map, ← stdAt, hstd, seam_lat_eq_map, localization_map_seamVec]

end GlobalTheory.FrameLat

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeamTwist

theorem seamHom_smul {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : X.E) (x : HomE D.host.E a b) :
    seamHom s (s.iE r • x) = r • seamHom s x := by
  refine LinearMap.ext fun w => funext fun l => s.iE.injective ?_
  rw [seamHom_apply]
  show s.iE r * x (fun k => s.iE (w k)) l = s.iE (r * seamHom s x w l)
  rw [map_mul, seamHom_apply]

theorem seamHom_smul_int {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : 𝓞 X.E) (x : HomE D.host.E a b) :
    seamHom s (RingOfIntegers.mapRingEquiv s.iE r • x) = r • seamHom s x :=
  seamHom_smul s (r : X.E) x

theorem seamHom_mem_locP {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b))
    (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)) (h : ∀ x, seamHom s x ∈ M ↔ x ∈ M') (P : HeightOneSpectrum (𝓞 X.E))
    (x : HomE D.host.E a b) :
    seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
  show (∃ r ∈ P.asIdeal.primeCompl, r • seamHom s x ∈ M) ↔ ∃ r ∈ (seamP s P).asIdeal.primeCompl, r • x ∈ M'
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, fun hh => hr ((mem_seamP s P r).1 hh), (h _).1 ?_⟩
    rwa [seamHom_smul_int]
  · rintro ⟨r, hr, hm⟩
    obtain ⟨r, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
    refine ⟨r, fun hh => hr ((mem_seamP s P r).2 hh), ?_⟩
    rw [← seamHom_smul_int]
    exact (h _).2 hm

theorem seamHom_mem_twO : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  intro D X s a b M M' h cl e e' he x
  have key : ∀ P : HeightOneSpectrum (𝓞 X.E),
      ((cl : X.E) ^ e P)⁻¹ • seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔
        ((cl : D.host.E) ^ e' (seamP s P))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
    intro P
    rw [← seamHom_smul, seamHom_mem_locP s M M' h, he, map_inv₀, map_zpow₀, map_natCast]
  unfold twist₂
  rw [Submodule.mem_iInf, Submodule.mem_iInf]
  constructor
  · intro hx Q
    obtain ⟨P, rfl⟩ : ∃ P, seamP s P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).surjective Q
    exact (key P).1 (hx P)
  · intro hx P
    exact (key P).2 (hx (seamP s P))

end GlobalTheory.SeamTwist
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetLoc

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_qOf_pow (P : HeightOneSpectrum (𝓞 E)) (t : ℕ) : IntAt P ((qOf P : E) ^ t) := by
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ t)

theorem congr_of_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (D a k : ℕ) (hak : a + k ≤ D)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (g z - z) ∈ stdAt E n P)
    (y0 x : Sp E n) (hy : ∀ l, IntAt P ((qOf P : E) ^ a * y0 l))
    (hx : ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (x - y0) l)) :
    ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (g x - y0) l) := by
  have hc : (qOf P : E) ≠ 0 := qOf_ne_zero P
  have hxa : ∀ l, IntAt P ((qOf P : E) ^ a * x l) := fun l => by
    have e : (qOf P : E) ^ a * x l = (qOf P : E) ^ a * y0 l + (qOf P : E) ^ (a + k) * (((qOf P : E) ^ k)⁻¹ * (x - y0) l) := by
      simp only [Pi.sub_apply]
      rw [pow_add]
      field_simp
      ring
    rw [e]
    exact (hy l).add ((intAt_qOf_pow P _).mul (hx l))
  have hz : (qOf P : E) ^ a • x ∈ stdAt E n P := (mem_localization_standardLattice P _).2 fun l => by simpa using hxa l
  have h1 := (mem_localization_standardLattice P _).1 (hg _ hz)
  obtain ⟨t, ht⟩ : ∃ t, D = t + (a + k) := ⟨D - (a + k), by omega⟩
  intro l
  have e : ((qOf P : E) ^ k)⁻¹ * (g x - y0) l = ((qOf P : E) ^ k)⁻¹ * (x - y0) l +
      (qOf P : E) ^ t * ((((qOf P : E) ^ D)⁻¹ • (g ((qOf P : E) ^ a • x) - (qOf P : E) ^ a • x)) l) := by
    rw [map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    simp only [pow_add]
    field_simp
    ring
  rw [e]
  exact (hx l).add ((intAt_qOf_pow P t).mul (h1 l))

theorem symm_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (D : ℕ) (hk : κ ∈ GLint E n P)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ z - z) ∈ stdAt E n P) :
    ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) ∈ stdAt E n P := by
  intro z hz
  have hk' : ∀ x, κ x ∈ stdAt E n P ↔ x ∈ stdAt E n P := hk
  have hz' : κ.symm z ∈ stdAt E n P := (hk' _).1 (by simpa using hz)
  have h := hg _ hz'
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) = -(((qOf P : E) ^ D)⁻¹ • (z - κ.symm z)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact (stdAt E n P).neg_mem h

end Local

end GlobalTheory.CosetLoc

namespace GlobalTheory.CosetLoc


open Classical in
theorem sameCoset_symm_iff : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  intro X Pr sel S mu cst P n κ y0 hc hk hg hD hy1 hy2 w
  have hg' := symm_sub_one κ (cst.D P) hk hg

  obtain ⟨a, hak, hy⟩ : ∃ a, a + (if P.1 ∈ Pr.vGs then 0 else cst.M) ≤ cst.D P ∧ ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ a * y0 l) := by
    by_cases hP : P.1 ∈ Pr.vGs
    · refine ⟨1, ?_, fun l => by simpa using hy1 hP l⟩
      rw [if_pos hP]
      simpa using hc.D_pos P
    · refine ⟨cst.M, ?_, hy2 hP⟩
      rw [if_neg hP]
      have := hD hP
      omega
  unfold SameCoset
  constructor
  · intro h
    have := congr_of_sub_one κ (cst.D P) a _ hak hg y0 (κ.symm w) hy h
    simpa using this
  · intro h
    exact congr_of_sub_one κ.symm (cst.D P) a _ hak hg' y0 w hy h

end GlobalTheory.CosetLoc
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, h⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y = x at h
    rw [Units.val_one, Matrix.one_mulVec] at h
    simpa [h] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x = x
    rw [Units.val_one, Matrix.one_mulVec]

theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory



theorem funMoved_mul_level : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  intro D X s i hi T bad lev ST SG P v h ι x κ d
  unfold FunMoved
  intro H w hw z hz
  have hU := (lev.U_eq κ.1).1 κ.2
  have hk : bc (prV (E := D.host.E) v) κ.1 ∈ lev.Uloc v := hU.2 v
  rw [lev.UlocAlt v h] at hk
  have hk2 := (Subgroup.mem_inf.1 hk).2
  change ∃ _, _ at hk2
  obtain ⟨hst, hf⟩ := hk2
  have hp : pullV (F := D.host.F) (x * κ.1) (fun a => s.iE (w a)) =
      (κ.1⁻¹).val *ᵥ pullV (F := D.host.F) x (fun a => s.iE (w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hz1 : z.1 = (bc (prV (E := D.host.E) v) κ.1⁻¹).val *ᵥ
      (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) := by
    rw [hz, hp]
    funext l
    exact RingHom.map_mulVec _ _ _ l
  have hz0 : (bc (prV (E := D.host.E) v) κ.1).val *ᵥ z.1 =
      fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l) := by
    have e : (bc (prV (E := D.host.E) v) κ.1).val * (bc (prV (E := D.host.E) v) κ.1⁻¹).val = 1 := by
      rw [← Units.val_mul (bc (prV (E := D.host.E) v) κ.1), ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine (congrArg (fun y => (bc (prV (E := D.host.E) v) κ.1).val *ᵥ y) hz1).trans ?_
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  rw [H w hw ⟨_, (hst z.1).1 z.2⟩ hz0]
  exact congrArg ι (hf z)

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

theorem _root_.GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  first | exact @GlobalTheory.TwU.seamP_under_eq | exact GlobalTheory.TwU.seamP_under_eq | (intros; apply GlobalTheory.TwU.seamP_under_eq <;> assumption)
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (g : GL (Fin N) E), GlobalTheory.TwU.CongAt (F := F) Q n (GlobalTheory.TwU.ratA F g) → ∀ a b : Fin N, Formalism.L2.Col.IntAt Q ((((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b)) := by
  first | exact @GlobalTheory.TwU.ratA_congAt_entry | exact GlobalTheory.TwU.ratA_congAt_entry | (intros; apply GlobalTheory.TwU.ratA_congAt_entry <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | exact GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | (intros; apply GlobalTheory.LatCoCompan.latCo_eq_latAd_compan <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  first | exact @GlobalTheory.LiftPolar.main | exact GlobalTheory.LiftPolar.main | (intros; apply GlobalTheory.LiftPolar.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteDatum_level_preserved_unitary_lattice_changes : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : HomE D.host.E a b → ℂ) (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E), e * star e = 1 → e' * star e' = 1 → DatLoc D cc SS cl (SDLat.smulLat e N) (SDLat.smulLat e' N') (fun x => Ξ (Matrix.toLin' (star e') ∘ₗ x ∘ₗ Matrix.toLin' e)) → DatLoc D cc SS cl N N' Ξ := by
  first | exact @GlobalTheory.TwV.datLoc_of_move | exact GlobalTheory.TwV.datLoc_of_move | (intros; apply GlobalTheory.TwV.datLoc_of_move <;> assumption)
end
