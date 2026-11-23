module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle951
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle953
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle955
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.homGlue_pt_ext_of_openCover : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (y y' : HomGlue.Pt A B L M Z), (∀ i, y.map hL hM (𝒰.f i) = y'.map hL hM (𝒰.f i)) → y = y' := by
  first | exact @GlobalTheory.EndLoc.HomGlue.Pt.ext_cover | exact GlobalTheory.EndLoc.HomGlue.Pt.ext_cover | (intros; apply GlobalTheory.EndLoc.HomGlue.Pt.ext_cover; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_glued_morphism_of_compatible_family : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), ∀ i, 𝒰.f i ≫ t = (x i).t ∧ ∀ e : pullback A.hom (x i).t ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ → e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒰.f i → e ≫ f = (x i).f := by
  first | exact @GlobalTheory.EndLoc.HomGlue.exists_glue_data | exact GlobalTheory.EndLoc.HomGlue.exists_glue_data | (intros; apply GlobalTheory.EndLoc.HomGlue.exists_glue_data; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.glue_wit_alt : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), (∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)) → HomGlue.Wit A B L M t f := by
  first | exact @GlobalTheory.EndLoc.HomGlue.glue_wit | exact GlobalTheory.EndLoc.HomGlue.glue_wit | (intros; apply GlobalTheory.EndLoc.HomGlue.glue_wit <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_nsmul_sub_eff : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  intro R _ Y f _ H m s M hH hM hs
  have hD : (dual M).IsLB := isLB_dual hM
  obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero R Y f H m s (dual M) hH hD hs
  refine ⟨(max t₀ 0).toNat, ?_⟩
  have hc : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  obtain ⟨σ, i, hσ⟩ := ht _ hc
  have key := eff_of_sec _ (isLB_tw hD hH _) σ i hσ
  have e : cls (tw (dual M) H ((max t₀ 0).toNat : ℤ)) (isLB_tw hD hH _) =
      cls (dual M) hD - cls (pw H (-((max t₀ 0).toNat : ℤ))) (isLB_pw hH _) :=
    cls_div hD (isLB_pw hH _) (isLB_tw hD hH _)
  rw [e, cls_pw hH, cls_dual hM hD, neg_zsmul, natCast_zsmul] at key
  convert key using 1
  abel
end GlobalTheory.EffBound
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_sec_of_eff {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (h : Eff (cls N hN)) :
    ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  obtain ⟨N', hN', hc, σ, j, hj⟩ := h
  obtain ⟨w, hw⟩ := (cls_eq_iff hN' hN).1 hc
  let e : LB.Sec N' ≃ₗ[Γ(X, ⊤)] LB.Sec N :=
    (SecOn.topEquiv N').symm ≪≫ₗ SecOn.congr hN' hN w hw ⊤ ≪≫ₗ SecOn.topEquiv N
  have hσ : σ ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have he : e σ ≠ 0 := by
    intro h0
    exact hσ (e.injective (h0.trans (map_zero e).symm))
  by_contra hne
  push_neg at hne
  exact he (HighTwist.sec_eq_zero _ (hne (e σ)))

end GlobalTheory.EffBound
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes
open Formalism.MainNotions.DIV.Inh (aPlusQ_anti aMinusQ_mono)

namespace GlobalTheory.BlockRows

theorem floor_cast_of_int {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem one_le_aPlusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : 1 ≤ DV.aPlusQ D j τ i := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  exact (DV.aPlusQ_last D j h1 h2 τ).trans
    (aPlusQ_anti D j τ (show i.1 ≤ D.R.k + j - 1 - 1 by omega) (by omega))

theorem one_le_aMinusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c < D.R.m) :
    1 ≤ DV.aMinusQ D j τ c :=
  (DV.aMinusQ_last D j h1 (by omega) τ).trans (aMinusQ_mono D j τ (Nat.zero_le c) hc)

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem aPlus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (i : Fin (D.R.sigW j).1) : DV.aPlus D j τ i ≤ 3 * L.sc.b ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  have h0 : 0 < D.R.k - 1 := by omega
  have a1 := aPlusQ_anti D j τ (Nat.zero_le i.1) (by omega)
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aPlusQ D j τ 0 ≤ (D.hc τ).v ⟨0, h0⟩ + (D.hc τ).e ⟨j - 1, hj⟩ := by
    rw [DV.aPlusQ_eq]
    unfold DV.sigPar DV.eQ
    rw [dite_eq_left h0, dite_eq_left ⟨h1, h2⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hk' : (2 : ℚ) ≤ D.R.k := by exact_mod_cast (show 2 ≤ D.R.k by omega)
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith
  have a3 : DV.aPlus D j τ i ≤ (((D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aPlus
    exact_mod_cast a1.trans a2
  have b1 := (L.cloud_v τ ⟨0, h0⟩).2
  have b2 := L.b_le τ ⟨j - 1, hj⟩
  have b3 := (abs_le.1 (L.be_close τ ⟨j - 1, hj⟩ ⟨j - 1, hj⟩)).1
  have b4 := one_le_b L.sc
  push_cast at b3
  have := hL.1
  have := hL.2
  nlinarith

theorem aMinus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (c : ℕ) (hc : j + c < D.R.m) : DV.aMinus D j τ c ≤ 3 * L.sc.b ^ 2 := by
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aMinusQ D j τ c ≤ (D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ := by
    unfold DV.aMinusQ DV.eQ
    rw [dite_eq_left hc, dite_eq_left ⟨h1, by omega⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hc' : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    linarith
  have a3 : DV.aMinus D j τ c ≤ (((D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aMinus
    exact_mod_cast a2
  have b3 := (abs_le.1 (L.be_close τ ⟨j + c, hc⟩ ⟨j - 1, hj⟩)).2
  have b4 := one_le_b L.sc
  have := hL.1
  nlinarith

theorem rows_sizes : ∀ (D : D7) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, (Antitone (rowsP D j τ) ∧ (∀ i, 1 ≤ rowsP D j τ i) ∧ ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i) ∧ (Antitone (rowsM D j τ) ∧ (∀ i, 1 ≤ rowsM D j τ i) ∧ ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)) ∧ ∀ L : SizeData₂ D, WindowsLe L → (∀ i, (rowsP D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2) ∧ ∀ i, (rowsM D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2 := by
  intro D j h1 h2 τ
  have hk := D.R.m_add_three_le_k
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hM : ∀ i : Fin (D.R.sigW j).2, j + ((D.R.sigW j).2 - 1 - i) < D.R.m := by
    intro i
    have := i.2
    omega
  have eP : ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i := by
    intro i
    have := floor_cast_of_int (DV.aPlusQ_int D j τ i) (one_le_aPlusQ D j h1 h2 τ i)
    unfold DV.aPlus rowsP
    rw [← this]
    simp
  have eM : ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i) := by
    intro i
    have := floor_cast_of_int (DV.aMinusQ_int D j τ _) (one_le_aMinusQ D j h1 τ _ (hM i))
    unfold DV.aMinus rowsM
    rw [← this]
    simp
  refine ⟨⟨?_, ?_, eP⟩, ⟨?_, ?_, eM⟩, fun L hL => ⟨fun i => ?_, fun i => ?_⟩⟩
  · intro a b hab
    have hb : b.1 < D.R.k + j - 1 := b.2
    exact Nat.floor_le_floor (aPlusQ_anti D j τ (show a.1 ≤ b.1 from hab) (by omega))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aPlusQ D j h1 h2 τ i)
  · intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    exact Nat.floor_le_floor (aMinusQ_mono D j τ (by omega) (hM a))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aMinusQ D j h1 τ _ (hM i))
  · rw [eP]
    exact aPlus_le D j h1 h2 τ L hL i
  · rw [eM]
    exact aMinus_le D j h1 τ L hL _ (hM i)

end GlobalTheory.BlockRows
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

theorem laurentConst_eq_of_tendsto :
    ∀ (h : ℂ → ℂ) (s₀ c c' : ℂ), LaurentConst h s₀ c → Tendsto h (𝓝[≠] s₀) (𝓝 c') → c = c' := by
  rintro h s₀ c c' ⟨p, hp0, hp⟩ hh
  have h1 : Tendsto (fun s : ℂ => p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 (c' - c)) := by
    refine (hh.sub hp).congr fun s => ?_
    ring
  have h2 : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).tendsto s₀
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.2 hs
  have h3 : Tendsto (fun s : ℂ => ‖(s - s₀)⁻¹‖) (𝓝[≠] s₀) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp h2)
  by_cases hd : 0 < p.degree
  · exact absurd (p.tendsto_norm_atTop hd h3) (not_tendsto_atTop_of_tendsto_nhds h1.norm)
  · have hp' : p = 0 := by
      rw [Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd), hp0, map_zero]
    subst hp'
    simp only [Polynomial.eval_zero, sub_zero] at hp
    exact tendsto_nhds_unique hp hh

end GlobalTheory.ThetaInner
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

theorem _root_.GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  first | exact @GlobalTheory.BrCoefFock.fockB_zmon_emb | exact GlobalTheory.BrCoefFock.fockB_zmon_emb | (intros; apply GlobalTheory.BrCoefFock.fockB_zmon_emb <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem comap_map_C_mapRingHom {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (p₁ : Ideal A₁) :
    (p₁.map (Polynomial.C : A₁ →+* A₁[X])).comap (Polynomial.mapRingHom f) =
      (p₁.comap f).map (Polynomial.C : A →+* A[X]) := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem atPrime_isDomain_injective (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] :
    IsDomain (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  obtain ⟨hd, -⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  refine ⟨hd, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_mem_height_le_one : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    hq hqu htor a ha hhyp P₁ _ hP₁ hfa
  obtain ⟨hRd, hRi⟩ := atPrime_isDomain_injective A EA QA
  obtain ⟨hR₁d, hR₁i⟩ := atPrime_isDomain_injective A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj)
  have hfa0 : f a ≠ 0 := fun h => ha (hf (by rw [h, map_zero]))
  obtain ⟨hp₁h, hX₁⟩ := GlobalTheory.T.height_one_contraction_of_etale_prime A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ (f a)
    hfa0 hfa hP₁
  obtain ⟨hph, π, hπ, y, hy⟩ := hhyp _ hp₁h (by rw [Ideal.mem_comap]; exact hfa)
  obtain ⟨⟨_, hdvr₁⟩, -⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ _
    hp₁h hX₁
  have hsq : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj)).comp (Polynomial.mapRingHom f) := by
    apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA),
      locBC_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA)]
    congr 1
    rw [inclE_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hPX : (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)).comap
      (algebraMap A[X] (Localization.AtPrime QA)) =
      ((P₁.comap (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comap f).map
        (Polynomial.C : A →+* A[X]) := by
    rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, hX₁, comap_map_C_mapRingHom]
  obtain ⟨⟨_, hdvr⟩, hirr⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A EA QA (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)) _
    hph hPX
  have hsqA : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f := by
    apply RingHom.ext; intro x
    exact locBC_algebraMap_base f i i₁ EA QA jA hcomp hj x
  have hsqF : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj)
        (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) := by
    apply RingHom.ext; intro x
    exact fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf x
  exact GlobalTheory.T.generic_fibre_base_change_injective A (Localization.AtPrime QA) hRi A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) hR₁i
    f hf _ hsqA _ hsqF DA q actA hq hqu htor P₁ hdvr₁ hdvr π (hirr π hπ)
    (algebraMap A₁ _ y) (by rw [← map_pow, hy, ← RingHom.comp_apply, ← hsqA, RingHom.comp_apply])

end GlobalTheory.KeyOriginBC
end
end

section

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.FockAlg.HarmStable MvPolynomial

namespace GlobalTheory.FockAlg.FinHarm

variable {σ : Type}

def lowDeg (σ : Type) (N : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨆ d : Fin (N + 1), homog σ d

instance [Finite σ] (N : ℕ) : FiniteDimensional ℂ (lowDeg σ N) := by
  haveI : ∀ d : ℕ, FiniteDimensional ℂ (homog σ d) := fun d =>
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  unfold lowDeg
  infer_instance

theorem mem_lowDeg_self (P : MvPolynomial σ ℂ) : P ∈ lowDeg σ P.totalDegree := by
  obtain ⟨N, hN⟩ : ∃ N, N = P.totalDegree := ⟨_, rfl⟩
  rw [← hN]
  have hs := sum_homogeneousComponent P
  rw [← hN] at hs
  rw [← hs]
  refine Submodule.sum_mem _ fun e he => ?_
  have he' : e < N + 1 := Finset.mem_range.1 he
  exact Submodule.mem_iSup_of_mem (⟨e, he'⟩ : Fin (N + 1))
    (homogeneousComponent_mem e P)

theorem DegZero.map_lowDeg {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (N : ℕ)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowDeg σ N) : K P ∈ lowDeg σ N := by
  have hle : lowDeg σ N ≤ (lowDeg σ N).comap K :=
    iSup_le fun d x hx => Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem d (hK d x hx))
  exact hle hP

end GlobalTheory.FockAlg.FinHarm

namespace GlobalTheory.FockAlg

open FinHarm

theorem fin_harm : ∀ (P Q R S : ℕ) (h : Pol P Q R S), h ∈ harm2 P Q R S →
    ∃ H0 : Submodule ℂ (Pol P Q R S), FiniteDimensional ℂ H0 ∧ h ∈ H0 ∧
      (∀ v ∈ H0, v ∈ harm2 P Q R S) ∧ KStable (fockAct1 P Q R S) H0 ∧
      KStable (fockAct2 P Q R S) H0 := by
  intro P Q R S h hh
  have hh' : h ∈ sub2 P Q R S := by
    rw [← SetLike.mem_coe, coe_fockHarmonicsSecondMemberSubmodule]; exact hh
  refine ⟨sub2 P Q R S ⊓ lowDeg _ h.totalDegree, ?_, ⟨hh', mem_lowDeg_self h⟩, ?_, ?_, ?_⟩
  · exact Submodule.finiteDimensional_of_le inf_le_right
  · intro v hv
    rw [← coe_fockHarmonicsSecondMemberSubmodule]; exact hv.1
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct1 hY) _ hw.2⟩
  · intro Y hY w hw
    exact ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, DegZero.map_lowDeg (degZero_fockAct2 hY) _ hw.2⟩

end GlobalTheory.FockAlg
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem _root_.GlobalTheory.T.nonempty_tensor_lineBundle_globalSections_equiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB → Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)] LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  first | exact @GlobalTheory.SecTensor.tensorSecEquiv | exact GlobalTheory.SecTensor.tensorSecEquiv | (intros; apply GlobalTheory.SecTensor.tensorSecEquiv <;> assumption)
end
