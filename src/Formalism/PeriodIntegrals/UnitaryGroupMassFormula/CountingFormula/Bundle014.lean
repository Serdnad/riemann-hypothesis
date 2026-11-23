module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_sum_left (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (w : (VS D).V) : (VS D).hT (∑ a ∈ s, c a • e a) w = ∑ a ∈ s, star (c a) * (VS D).hT (e a) w := by

  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sum_right (D : Formalism.BasicNotions.D7) {ι : Type} (s : Finset ι) (c : ι → D.host.E) (e : ι → (VS D).V)
    (v : (VS D).V) : (VS D).hT v (∑ a ∈ s, c a • e a) = ∑ a ∈ s, c a * (VS D).hT v (e a) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul]

theorem hT_swap (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have h := (VS D).herm.eq x y
  rw [starRingEnd_apply] at h
  exact h.symm

theorem pW_dec (D : Formalism.BasicNotions.D7) (v : (VS D).V) :
    v = pW D v + ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a + ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
      - ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm := by
  unfold pW
  abel

theorem delta_zero {K : Type} [Field K] [StarRing K] {r : ℕ} (β Δ : Matrix (Fin r) (Fin (r + 1)) K)
    (R : Matrix (Fin (r + 1)) (Fin r) K) (hR : β * R = 1) (hΔR : Δ * R = 0)
    (hM : Δ.conjTranspose * β + β.conjTranspose * Δ = 0) : Δ = 0 := by
  have h : (Δ.conjTranspose * β + β.conjTranspose * Δ) * R = (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * R := by rw [hM]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hR, hΔR, Matrix.mul_one, Matrix.mul_zero,
    add_zero, Matrix.zero_mul] at h
  rw [← Matrix.conjTranspose_conjTranspose Δ, h, Matrix.conjTranspose_zero]

theorem finite_level_index : FinK := by
  intro D T T' F0 Λ hF Z R hR Wf Af hWf hAf
  obtain ⟨-, -, hFe, -, c, hc, hFz⟩ := hF
  have hE : ∀ x, Good D T' F0 Λ Z x → ∀ (a : Fin D.R.rS) b,
      (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro x hx a b
    have h := hx.2.1 (Fin.castSucc a) b
    simp only [brS, FlagG.fvec, Fin.snoc_castSucc, hFe] at h
    simpa [betaZ] using h
  have hzm : ∀ x, Good D T' F0 Λ Z x → ∀ b,
      star c * (VS D).hT D.sp.zm (fr D x b) = Z (Fin.last _) b := by
    intro x hx b
    have h := hx.2.1 (Fin.last _) b
    simp only [brS, FlagG.fvec, Fin.snoc_last, hFz] at h
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h
    exact h
  have pW_sub : ∀ v v' : (VS D).V, pW D (v - v') = pW D v - pW D v' := by
    intro v v'
    simp only [pW, map_sub, sub_smul, Finset.sum_sub_distrib, sub_div]
    abel
  refine Set.Finite.of_injOn (f := fun x => (pWf D x, alM D x * R)) (t := Wf ×ˢ Af) ?_ ?_
    (hWf.prod hAf)
  · intro x hx
    exact ⟨hx.2.1, hx.2.2⟩
  intro x hx x' hx' hxx'
  obtain ⟨hp, hal⟩ := Prod.mk.inj hxx'
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = alM D x - alM D x' := ⟨_, rfl⟩
  have huE : ∀ a b, (VS D).hT (D.sp.hypE a) (fr D x b - fr D x' b) = 0 := by
    intro a b
    rw [map_sub, hE x hx.1, hE x' hx'.1, sub_self]
  have huz : ∀ b, (VS D).hT D.sp.zm (fr D x b - fr D x' b) = 0 := by
    intro b
    have hsc : star c ≠ 0 := star_ne_zero.mpr hc
    have h0 : star c * ((VS D).hT D.sp.zm (fr D x b) - (VS D).hT D.sp.zm (fr D x' b)) = 0 := by
      rw [mul_sub, hzm x hx.1, hzm x' hx'.1, sub_self]
    rw [map_sub]
    exact (mul_eq_zero.mp h0).resolve_left hsc
  have huF : ∀ a b, (VS D).hT (D.sp.hypF a) (fr D x b - fr D x' b) = Δ a b := by
    intro a b
    rw [hΔ, Matrix.sub_apply, map_sub]
    rfl
  have hupW : ∀ b, pW D (fr D x b - fr D x' b) = 0 := by
    intro b
    rw [pW_sub]
    have h := congrFun hp b
    simp only [pWf] at h
    rw [h, sub_self]
  have hu : ∀ b, fr D x b - fr D x' b = ∑ a, Δ a b • D.sp.hypE a := by
    intro b
    conv_lhs => rw [pW_dec D (fr D x b - fr D x' b)]
    simp only [hupW, huE, huz, huF, zero_smul, Finset.sum_const_zero, zero_div, zero_add, add_zero,
      sub_zero]
  have hΔR : Δ * R = 0 := by
    rw [hΔ, Matrix.sub_mul, hal, sub_self]
  have hM : Δ.conjTranspose * betaZ D Z + (betaZ D Z).conjTranspose * Δ = 0 := by
    ext a b
    have hG : (VS D).hT (fr D x a) (fr D x b) = (VS D).hT (fr D x' a) (fr D x' b) := by
      rw [hx.1.2.2 a b, hx'.1.2.2 a b]
    have hxa : fr D x a = fr D x' a + ∑ c, Δ c a • D.sp.hypE c := by
      rw [← hu a]
      abel
    have hxb : fr D x b = fr D x' b + ∑ c, Δ c b • D.sp.hypE c := by
      rw [← hu b]
      abel
    rw [hxa, hxb] at hG
    simp only [map_add (f := _), LinearMap.add_apply] at hG
    have h1 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (∑ c, Δ c b • D.sp.hypE c) = 0 := by
      rw [hT_sum_left]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hT_sum_right]
      simp [D.sp.hyp_ee]
    have h2 : (VS D).hT (fr D x' a) (∑ c, Δ c b • D.sp.hypE c) =
        ((betaZ D Z).conjTranspose * Δ) a b := by
      rw [hT_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, ← hE x' hx'.1 c a, hT_swap D (D.sp.hypE c) (fr D x' a)]
      ring
    have h3 : (VS D).hT (∑ c, Δ c a • D.sp.hypE c) (fr D x' b) = (Δ.conjTranspose * betaZ D Z) a b := by
      rw [hT_sum_left, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.conjTranspose_apply, hE x' hx'.1 c b]
    rw [Matrix.add_apply, Matrix.zero_apply, ← h2, ← h3]
    rw [h1, add_zero] at hG
    linear_combination hG
  have hΔ0 : Δ = 0 := delta_zero (betaZ D Z) Δ R hR hΔR hM
  have hfr : ∀ b, fr D x b = fr D x' b := by
    intro b
    have h := hu b
    rw [hΔ0] at h
    simp only [Matrix.zero_apply, zero_smul, Finset.sum_const_zero] at h
    exact sub_eq_zero.mp h
  refine Prod.ext (funext fun i => ?_) ?_
  · have h := hfr (Fin.castSucc i)
    simpa [fr] using h
  · have h := hfr (Fin.last _)
    simpa [fr] using h

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnimodOneGenus : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate →
    ∀ L M : Submodule (𝓞 K) V, Submodule.IsLattice K L → Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.IsUnimodular h L → Formalism.HermitianLatticesTheory.IsUnimodular h M → Formalism.HermitianLatticesTheory.SameGenus h L M

section Constr

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

def aaI (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

def PartnerOK (f : Fin D.R.rS → (VS D).V) : Prop :=
  (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, (VS D).hT (f a) (f b) = 0) ∧
    ∀ a, (VS D).hT (f a) F0.z = 0

def vPr (f : Fin D.R.rS → (VS D).V) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (F0.e a) v • f a

theorem vPr_add (f : Fin D.R.rS → (VS D).V) (v w : (VS D).V) :
    vPr D F0 f (v + w) = vPr D F0 f v + vPr D F0 f w := by
  simp only [vPr, map_add (f := _), add_smul, Finset.sum_add_distrib]
  abel

theorem vPr_smul (f : Fin D.R.rS → (VS D).V) (c : D.host.E) (v : (VS D).V) :
    vPr D F0 f (c • v) = c • vPr D F0 f v := by
  simp only [vPr, map_smul, smul_eq_mul, mul_smul, smul_sub, Finset.smul_sum]

theorem vPr_zero (f : Fin D.R.rS → (VS D).V) : vPr D F0 f 0 = 0 := by
  simp [vPr]

theorem fi_add {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x y : D.host.E}
    (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  have h := Submodule.add_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.mem_coe.mpr hx) (FractionalIdeal.mem_coe.mpr hy)
  exact FractionalIdeal.mem_coe.mp h

theorem fi_zero (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : (0 : D.host.E) ∈ I := by
  exact FractionalIdeal.mem_coe.mp (Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E))

theorem fi_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (o : 𝓞 D.host.E) {x : D.host.E}
    (hx : x ∈ I) : (o : D.host.E) * x ∈ I := by
  have h := Submodule.smul_mem (I : Submodule (𝓞 D.host.E) D.host.E) o (FractionalIdeal.mem_coe.mpr hx)
  rw [Algebra.smul_def] at h
  exact FractionalIdeal.mem_coe.mp h

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) o, rfl⟩

def lamC (f : Fin D.R.rS → (VS D).V) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) :
    Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {v | (∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
    (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧ (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
    ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a}
  add_mem' := by
    rintro v v' ⟨h1, ⟨w, hw, hwM⟩, h3⟩ ⟨h1', ⟨w', hw', hwM'⟩, h3'⟩
    refine ⟨fun a => ?_, ⟨w + w', ?_, ?_⟩, fun a => ?_⟩
    · rw [map_add (f := _), star_add]; exact fi_add D (h1 a) (h1' a)
    · rw [Submodule.coe_add, hw, hw', vPr_add]
    · rw [Submodule.Quotient.mk_add]; exact M.add_mem hwM hwM'
    · rw [vPr_add, map_add (f := _)]; exact fi_add D (h3 a) (h3' a)
  zero_mem' := by
    refine ⟨fun a => ?_, ⟨0, ?_, ?_⟩, fun a => ?_⟩
    · simp only [map_zero, star_zero]; exact fi_zero D _
    · simp [vPr_zero]
    · simp
    · simp only [vPr_zero, map_zero]; exact fi_zero D _
  smul_mem' := by
    rintro o v ⟨h1, ⟨w, hw, hwM⟩, h3⟩
    have hs : o • v = (o : D.host.E) • v := (algebraMap_smul D.host.E o v).symm
    refine ⟨fun a => ?_, ⟨o • w, ?_, ?_⟩, fun a => ?_⟩
    · obtain ⟨o', ho'⟩ := star_int D o
      rw [hs, map_smul, smul_eq_mul, star_mul, ← ho', mul_comm]
      exact fi_mul D o' (h1 a)
    · rw [hs, vPr_smul, ← hw]
      show o • (w : (VS D).V) = _
      exact (algebraMap_smul D.host.E o (w : (VS D).V)).symm
    · rw [Submodule.Quotient.mk_smul]; exact M.smul_mem o hwM
    · rw [hs, vPr_smul, map_smul, smul_eq_mul]; exact fi_mul D o (h3 a)

end Constr

def PartnerEx : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)), ∃ f, PartnerOK D F0 f

def LamLattice : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Submodule.IsLattice D.host.E (lamC D F0 f M)

def LamUnimod : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (lamC D F0 f M)

def LamFlag : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u)) (f : Fin D.R.rS → (VS D).V)
    (M : Submodule (𝓞 D.host.E) (WbQ D F0)), PartnerOK D F0 f → IsGlueLat (hWb D F0) (zbar D F0) M →
      F0.z ∈ lamC D F0 f M ∧ XLam (lamC D F0 f M) (lf D F0) = XS D F0 ∧
      (∀ c : D.host.E, c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) ∧
      Mof D F0 (lamC D F0 f M) = M

def LocGenXS : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ∃ c : Fin D.R.rS → D.host.E, (∀ a, c a ≠ 0) ∧
      (((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ a, c a = 1) ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XS D F0) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)))

private theorem row_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hL


theorem rowSurj_of (hJ : UnimodOneGenus) (hP : PartnerEx) (hL : LamLattice) (hU : LamUnimod)
    (hF : LamFlag) (hG : LocGenXS) : RowSurj := by
  intro D u F0 M hM
  obtain ⟨f, hf⟩ := hP D u F0
  obtain ⟨hz, hX, hprim, hMof⟩ := hF D u F0 f M hf hM
  have hLat := hL D u F0 f M hf hM
  have hUn := hU D u F0 f M hf hM
  have hFull : Submodule.IsFullLattice D.host.E (lamC D F0 f M) :=
    { toIsLattice := hLat, span_eq_top := row_span_eq_top_of_unimodular D hLat.fg hUn }
  refine ⟨lamC D F0 f M, ?_, hMof⟩
  refine ⟨?_, ⟨hLat, hUn, ⟨hz, rfl⟩, ?_, hprim⟩, hX⟩
  ·
    exact ⟨hFull, hJ D.host.E (VS D).V (VS D).hT D.sp.cm.cmUnram (VS D).herm (VS D).nondeg
      (VS D).L0 (lamC D F0 f M) (VS D).standardTuple_isLattice hLat (VS D).baseLattice_isUnimodular hUn⟩
  · intro P
    rw [hX]
    exact hG D u F0 P

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end
