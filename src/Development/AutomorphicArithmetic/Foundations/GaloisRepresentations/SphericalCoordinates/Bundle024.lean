module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.fixEq_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixEq := by
  intro hHC hOne hLat p _ D G L gb N N' h hLev X X' c₁ c₂ hX hL hX' hL' ρ hFine v t₀ B PD RD D' t hCls P j a hCo y hSees ga hga P₁ P₂ x₁ x₂ e₁ e₂ hU₁ hU₂ hP
  have hN3 : 3 ≤ N := hLev.1
  have hNp : N.Coprime p := hLev.2.1
  have hdvd : N ∣ N' := hLev.2.2.2.2.1
  obtain ⟨hPl, hCA, hLoc, -⟩ := hCo
  obtain ⟨-, hS1, hS2⟩ := hSees
  obtain ⟨D'', t'', P'', e'', inc, j'', hCls'', hU'', hPinc, he'', hd, hjinc, hPl'', hCA'', hLoc''⟩ :=
    hHC p D G L gb N N' h hLev X X' c₂ hX hL hX' hL' ρ hFine D' t P₁ x₁ e₁ hU₁ B j a.1.1 (PD.lat a.1.2) hPl hCA hLoc
  obtain ⟨e₂', hU₂', he₂'⟩ :=
    hOne p D G L gb N N' h hLev X X' c₁ hX hL hX' hL' ρ hFine B PD D' t hCls j a.1 hPl hCA hLoc P₂ x₂ e₂ hU₂
  have hCAN : IsCoordA L (trivX B) N D' t j a.1.1 := by
    refine ⟨hCA.1, fun b => ?_⟩
    obtain ⟨w, hw, hweq⟩ := hCA.2 b
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k • w, AddSubgroup.nsmul_mem _ hw k, ?_⟩
    rw [hweq, hk, mul_smul]
  have hmem1 : (a.1.1 * h⁻¹)⁻¹ * B.toAf y * a.1.1 ∈ L.KN N := by
    have hS1' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS1
    rw [mul_inv_rev, inv_inv]
    rw [mul_assoc h, mul_assoc h]
    exact hS1'
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B PD N (by omega) hNp D'' t'' D' t j'' j (a.1.1 * h⁻¹, a.1.2) a.1 N N' t'' t
      hCls'' hCls hPl'' hPl hCA'' hCAN hLoc'' hLoc y).mp ⟨hmem1, hS2⟩
  have hcancel : ∀ w' : VQ D, (actY L y) ((actY L y⁻¹) w') = w' := by
    intro w'
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hgi : ∀ u, w (ga u) = inc u := by
    intro u
    apply hPl''.1
    rw [hjinc, hwj, hga, hcancel]
  have hPw : ∀ x, P'' (w x) = P₂ x := by
    intro x
    obtain ⟨d, u, hd0, hdu⟩ := hd (w x)
    have hgu : ga u = d • x := by
      apply w.injective
      rw [hgi, hdu, map_nsmul]
    have h2 : d • P'' (w x) = d • P₂ x := by
      rw [← map_nsmul, ← map_nsmul, ← map_nsmul, ← hgu, hgi, hPinc, hP]
    exact smul_right_injective _ hd0 h2
  have hPw' : ∀ x, P'' (w x) = (LinearEquiv.refl ℂ (Fin D.g → ℂ)) (P₂ x) := fun x => hPw x
  have hpt : x₂ ≫ c₁.q = x₁ ≫ c₂.q :=
    hFine.sep D' D'' t t'' P₂ P'' _ _ e₂' e'' hU₂' hU'' w (LinearEquiv.refl ℂ _) hwm hPw'
  have hT := GlobalTheory.T.uniformisationAt_transport_isometry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w (LinearEquiv.refl ℂ _) (by omega) hU₂' hwm hPw' hU''.2.1
  have key : ∀ (y₁ y₂ : Sp ℂ ⟶ (gfam X.univ hX hL).X) (hy : y₁ = y₂)
      (f₁ : (Fin D.g → ℂ) → (Over.mk y₁ ⟶ (gfam X.univ hX hL).A))
      (f₂ : (Fin D.g → ℂ) → (Over.mk y₂ ⟶ (gfam X.univ hX hL).A)),
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₁ f₁ →
      UnifAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N D'' t'' P'' y₂ f₂ →
      ∀ z, Over.Hom.left (f₁ z) = Over.Hom.left (f₂ z) := by
    intro y₁ y₂ hy f₁ f₂ h₁ h₂ z
    subst hy
    rw [GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking _ _ _ _ _ _ _ _ _ _ _ _ _ f₁ f₂ hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D'' t'' hCls'') h₁ h₂]
  refine ⟨hpt.symm, fun z => ?_⟩
  rw [← he'' z, ← he₂' z]
  exact key _ _ hpt.symm e'' _ hU'' hT z
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem gUnif_of : ModelEx → GenCmp → GenPts → BaseC → GFine → GUnif := by
  intro hM hC hP hB hF p _ D ha hm t₀ ht ρ hρ gb hgb N hN hNp X
  obtain ⟨b, hbρ, hbt, hbT⟩ := hB p D ha hm t₀ ht ρ hρ gb hgb
  obtain ⟨M⟩ := hM p D ℂ b N hN hNp
  obtain ⟨j, hjo, hjc, hjs, hjG⟩ := hC p D ℂ b ℂ (RingHom.id ℂ) gb hbρ hbt N hN hNp M X
  have hpts := hP p D ℂ b (RingHom.id ℂ) gb hbρ hbt N hN hNp M X j hjo hjc hjs hjG
  obtain ⟨h, hL, -⟩ := model_uniformised p D ℂ b N (RingHom.id ℂ) ρ M hN hNp hbT
  have hfine := T.complexPoints_classify_markedPeriods p D ℂ b N (RingHom.id ℂ) ρ M h hL (by omega) hNp hbT
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by
    simp [spMap]
  have hsq : (j ≫ pullback.fst M.s (spMap (RingHom.id ℂ))) ≫ M.s = X.s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, hid, Category.comp_id]
  obtain ⟨hX, hL', hXf⟩ := hF p D b gb N M X ρ h hL _ hsq hjG hpts hfine
  haveI := hjo
  haveI := hjc
  have hsm : SmoothOfRelativeDimension (D.n - 1) X.s := by
    have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
    rw [ha, Nat.one_mul] at h1
    haveI : SmoothOfRelativeDimension (D.n - 1) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (D.n - 1)).of_isPullback
        (IsPullback.of_hasPullback _ _) h1
    have h3 : SmoothOfRelativeDimension (0 + (D.n - 1))
        (j ≫ pullback.snd M.s (spMap (RingHom.id ℂ))) := inferInstance
    rw [Nat.zero_add, hjs] at h3
    exact h3
  have hqc : QuasiCompact X.s := by
    haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
    rw [← hjs]
    infer_instance
  have hsep : IsSeparated X.s := by
    haveI : IsSeparated M.s := by
      obtain ⟨K, i, hi, -, hiK⟩ := M.qproj
      haveI := hi
      haveI := isProper_str ℂ K
      rw [← hiK]
      infer_instance
    rw [← hjs]
    infer_instance
  refine ⟨hsm, hqc, hsep, hX, hL', hXf, ?_⟩
  refine T.complexUniformisation_of_markedPeriods_family _ _ _ ρ _ (gfam X.univ hX hL') N (D.Cls N) (D.n - 1) hN ?_ hsm hqc
    (fun D' t ht => Datum.Cls.fullMark D N (by omega) hNp D' t ht) hXf
  intro a
  change X.univ.eta a ^ N = 1
  rw [← GObj.eta_nsmul, GObj.eta_ker]

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.stabTriv_of :
    UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.Rigid → UpperTheory.Gal.W2.StabTriv := by
  intro hOcc hLat hFix hRig p _ D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N hN3 hNp B a y hSees
  obtain ⟨D', t, P, j, hCls, hPer, hPl, hCA, hLoc, Q, hQ, hQj, hrel⟩ :=
    hOcc p D G L hDa hDm v hsig t₀ htau ρ hSig PD RD N (by omega) hNp B a
  obtain ⟨hFixL, hS1, hS2⟩ := hSees
  obtain ⟨w, hwm, hwj⟩ :=
    (hLat p D G L B (PD B) N (by omega) hNp D' t D' t j j a.1 a.1 N N t t
      hCls hCls hPl hPl hCA hCA hLoc hLoc y).mp ⟨hS1, hS2⟩
  obtain ⟨hiff, hinv⟩ := hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y
  obtain ⟨H, hH⟩ := hiff.mp hFixL
  obtain ⟨H', hH'⟩ := ((hFix p D G L v t₀ ρ B.β (RD B) Q a.2 hQ hrel y⁻¹).1).mp (hinv hFixL)
  have hback : ∀ x : VQ D, (actY L y⁻¹) ((actY L y) x) = x := by
    intro x
    simp only [actY]
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have key : ∀ z, (H' * H) *ᵥ z = z := by
    let f : (Fin D.g → ℂ) →ₗ[ℝ] (Fin D.g → ℂ) :=
      (Matrix.toLin' (H' * H)).restrictScalars ℝ - LinearMap.id
    have hle : Set.range Q ⊆ LinearMap.ker f := by
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      show Matrix.toLin' (H' * H) (Q x) - Q x = 0
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hH x, ← hH', hback, sub_self]
    intro z
    have hz : z ∈ LinearMap.ker f := by
      have hs := Submodule.span_le.mpr hle
      rw [hQ.2.1] at hs
      exact hs Submodule.mem_top
    rw [LinearMap.mem_ker] at hz
    have hz' : Matrix.toLin' (H' * H) z - z = 0 := hz
    rwa [Matrix.toLin'_apply, sub_eq_zero] at hz'
  have hHH : H' * H = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact LinearMap.ext fun z => by rw [Matrix.toLin'_apply, key]; rfl
  letI : Invertible H := invertibleOfLeftInverse H H' hHH
  have hfix : ∀ u, w u = u :=
    hRig D.O D.inv D.g ρ D.La N D' t P w (Matrix.toLinearEquiv' H this) hN3
      (GlobalTheory.UPel.HT.Datum.Cls.fullMark D N (by omega) hNp D' t hCls) hPer hwm
      (fun u => by
        rw [← hQj (w u), hwj, hH, hQj]
        show H *ᵥ P u = Matrix.toLin' H (P u)
        rw [Matrix.toLin'_apply])
  have hrep : L.rep ↑(↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, u, hm, hmu⟩ := hPl.2.2.1 x
    have h1 : m • (actY L y) x = m • x := by
      rw [← map_nsmul, hmu, ← hwj, hfix]
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hm) h1
  have hy1 : (↑y : G.Cˣ × ℚˣ).1 = 1 := by
    apply Units.ext
    apply L.rep_inj
    rw [hrep, Units.val_one, map_one]
  have hprop := y.2
  obtain ⟨hy, -⟩ := hprop
  rw [hy1] at hy
  have hsh : sh G (1 : G.C) = 1 := by simp [sh]
  rw [Units.val_one, _root_.one_mul, hsh, _root_.mul_one] at hy
  have hq : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    have : (algebraMap ℚ G.C) ((↑y : G.Cˣ × ℚˣ).2 : ℚ) * ↑B.β = 1 * ↑B.β := by rw [_root_.one_mul, ← hy]
    exact (Units.mul_left_inj B.β).mp this
  have hq' : ((↑y : G.Cˣ × ℚˣ).2 : ℚ) = 1 := by
    rw [← map_one (algebraMap ℚ G.C)] at hq
    exact (algebraMap ℚ G.C).injective hq
  apply Subtype.ext
  exact Prod.ext hy1 (Units.ext hq')
end
