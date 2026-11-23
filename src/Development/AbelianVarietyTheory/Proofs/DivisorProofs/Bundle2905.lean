module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle587
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
public import Mathlib.GroupTheory.CosetCover
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_realisedThetaSystem_of_universalSectionBasis : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.R = R ∧ ρ.n = n ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) := by
  first | exact @GlobalTheory.ThetaSBasis.exists_real_of_secBasis | exact GlobalTheory.ThetaSBasis.exists_real_of_secBasis | (intros; apply GlobalTheory.ThetaSBasis.exists_real_of_secBasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaSystem_realisation_regular_at_prime : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (𝔭 : Ideal R), 𝔭.IsPrime → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), (∀ x ∈ S.R, ∃ a b : R, b ∉ 𝔭 ∧ x = (a : Ω) / (b : Ω)) ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  first | exact @GlobalTheory.ThetaRealAt.exists_thetaSys_real_at | exact GlobalTheory.ThetaRealAt.exists_thetaSys_real_at | (intros; apply GlobalTheory.ThetaRealAt.exists_thetaSys_real_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.thetaPoint_conj_algClosure_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  first | exact @GlobalTheory.isThetaPt_conj | exact GlobalTheory.isThetaPt_conj | (intros; apply GlobalTheory.isThetaPt_conj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} := by
    have hsubset : {z : M.Z | q z = x} ⊆ (q ⁻¹ᵁ V : Set M.Z) := by
      intro z hz
      change q z ∈ V
      rw [hz]
      exact hxV
    exact fun a ha => M.ringOn_anti hsubset ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)

  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) := by
    refine GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => ?_
    rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K) with hz
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := by
    intro a ha
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have hcz := M.ringOn_le_O hzU hc
    have hdz := M.ringOn_le_O hzU hd
    have hq : c / d ∈ M.O z := ha
    have e1 := val_mul hsp hq hdz
    have e1' := val_mul hsp' hq hdz
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr hdz hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := by rw [← h d (hsub d hd)]; exact hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  have hW : z ∈ W := h₁ (x := IsLocalRing.closedPoint K) trivial
  ext f
  have e1 := val_valF ((top_le_preimage_iff y W).1 h₁) f
  have e2 := val_valF ((top_le_preimage_iff y' W).1 h₂) f
  have e3 := hO _ (valF_mem_O hW f)
  rw [e1, e2] at e3
  unfold valF at e3
  rw [dite_eq_left h₁, dite_eq_left h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  have hσB : ∀ (σ : L ≃ₐ[F] L) (b : L), b ∈ B → σ b ∈ B := fun σ b hb =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 hb))
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ =>
    ((σ : L →+* L).comp B.subtype).codRestrict B fun b => hσB σ b b.2
  have hσB_apply : ∀ σ (b : B), ((σB σ b : B) : L) = σ b := fun _ _ => rfl

  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := by
    intro b
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := by
      intro τ
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
      rfl
    have hcoeff : ∀ n, ∃ a : A, algebraMap A L a = (P.coeff n : L) := by
      intro n
      have hfix : ∀ τ : L ≃ₐ[F] L, τ (P.coeff n : L) = P.coeff n := by
        intro τ
        have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) (hPmap τ)
        simpa [Polynomial.coeff_map] using this
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 hfix
      change algebraMap F L f = _ at hf
      have hint : IsIntegral A (algebraMap F L f) := by rw [hf]; exact (hB _).1 (P.coeff n).2
      have hint' : IsIntegral A f := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective]
        exact hint
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have hmap : P.map e = P.map e' := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoeff n
      exact hA _ ⟨a, ha⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ =>
    (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun σ b => by
    simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨σ, hσ⟩ := claim b
    refine Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [zero_vadd]
    exact (hmemH σ b).2 hσ
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  have hcσ : c = σB σ b := Subtype.ext hc
  subst hcσ
  have hn : (H σ).index ≠ 0 := hfin.index_ne_zero
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  haveI : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := by
    intro b
    letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b := by
      constructor
      · intro hb
        exact IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb
      · intro hb
        refine IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => ?_) hb
        show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
        rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]
    rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hz : q (y (IsLocalRing.closedPoint K)) = z₁ := rfl
  have hz' : q (y' (IsLocalRing.closedPoint K)) = z₁ := by rw [hz₁, hyy]; rfl
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz'))
  have he : ∀ b : B, e b = M₂.val y b := fun _ => rfl
  have he' : ∀ b : B, e' b = M₂.val y' b := fun _ => rfl
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    rw [he, he', ← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  haveI := hF
  have key : y ≫ s = y' := by
    refine eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => ?_
    have hys : (y ≫ s) ≫ q = y ≫ q := by rw [Category.assoc, hs2]
    rw [hys] at hb
    have hbB : b ∈ B := hb
    have hσB : σ b ∈ B := (hB _).2
      (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hbB))
    rw [hs3]
    exact (hσ ⟨b, hbB⟩ ⟨σ b, hσB⟩ rfl).symm
  refine ⟨σ, s, hs1, key, fun b => ?_⟩
  rw [← key]
  exact hs3 K y b

end GlobalTheory.Poinc.FieldConj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_chart_map_to_normal_finite_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  first | exact @GlobalTheory.Poinc.ModelAt.exists_map_model | exact GlobalTheory.Poinc.ModelAt.exists_map_model | (intros; apply GlobalTheory.Poinc.ModelAt.exists_map_model <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.stalkHom_stalkMap_eq_functionFieldExtension : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (p : M₂.Z ⟶ M₁.Z), M₂.pt ≫ p = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₂ : M₂.Z) (x : M₁.Z.presheaf.stalk (p z₂)), M₂.stalkHom z₂ ((p.stalkMap z₂).hom x) = algebraMap Ω₁ Ω₂ (M₁.stalkHom (p z₂) x) := by
  first | exact @GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | exact GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap | (intros; apply GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ z₁ : M₁.Z, letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ (𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)), 𝔷.IsMaximal → ∀ z₂ : M₂.Z, q z₂ = z₁ → (∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M₂.Z), q (y (cPt p)) = z₁ → (∀ b ∈ 𝔷, ‖M₂.val (gPt p ≫ y) (b : Ω₂)‖ < 1) → y (cPt p) = z₂ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 z₂ hz₂ hmem p _ y hy hsmall
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN hF hg z₁
  have hO : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂) ∈ M₂.O (y (cPt p)) :=
    fun b => (h1 b).1 b.2 _ hy
  let ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O (y (cPt p)) :=
    (RingHom.id Ω₂).restrict _ _ fun c hc => hO ⟨c, hc⟩
  have hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O (y (cPt p)))).comap ι := by
    intro b hb
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (RatModel.norm_val_lt_one_iff rfl (hO b)).1 (hsmall b hb)
  have heq := h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle
  have key : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O (y (cPt p))) := by
    intro b
    rw [← hmem b, heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, RatModel.isUnit_O_iff]
    show ¬ ((b : Ω₂) ≠ 0 ∧ (b : Ω₂)⁻¹ ∈ M₂.O (y (cPt p))) ↔ _
    tauto
  refine (h3 z₂ (y (cPt p)) hz₂ hy fun b => ?_).symm
  by_cases hb0 : (b : Ω₂) = 0
  · rw [hb0, inv_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · have := key b
    simp only [hb0, false_or] at this
    exact not_iff_not.1 this
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ P : u.Λ →+ HdR A, (∀ c : primDR A, IsPer u.ex u.Λ (cmp1 (str A) c.1) fun l => P l c) → Submodule.span ℂ (Set.range P) = ⊤ ∧ Module.finrank ℂ (HdR A) = 2 * g := by
  first | exact @GlobalTheory.CechPer.span_periods_eq_top_and_finrank | exact GlobalTheory.CechPer.span_periods_eq_top_and_finrank | (intros; apply GlobalTheory.CechPer.span_periods_eq_top_and_finrank <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isSystem_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R))
    (t : ℕ → W.IdealSheafData), IsSystem f I t →
    ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme),
      (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧
      (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧
      ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  intro R _ I W f t ht
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
      Ideal.Quotient.mk_surjective
  have hmono : ∀ e, Mono (thick R I e) := fun e => by haveI := hci e; infer_instance
  have hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1)) := by
    intro e
    haveI := hci e
    have h := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W)
      (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance
      pullback.condition).1
      ⟨pullback.fst f (thick R I e), Category.comp_id _, by
        simpa using IsPullback.of_hasPullback f (thick R I e)⟩
    simpa using h.symm
  have hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker := fun e => by
    rw [hfst, Scheme.IdealSheafData.ker_subschemeι]
    exact ht.baseIdeal_le e
  let q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) := fun e =>
    haveI := hci e
    IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _
  have hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e := fun e => by
    haveI := hci e
    simp only [q, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  clear_value q
  have hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧
      IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e) := fun e =>
    (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e)
      inferInstance inferInstance (hq e)).2
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)
  choose β hβ using hb
  refine ⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩
  have hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e) := by
    haveI := hmono (e + 1)
    refine IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
      (fun s m _ h2 => by simpa using h2)
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]
    exact s.condition.symm
  have hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e := by
    haveI := hmono (e + 1)
    rw [← cancel_mono (thick R I (e + 1))]
    calc (β e ≫ q (e + 1)) ≫ thick R I (e + 1) = β e ≫ (t (e + 1)).subschemeι ≫ f := by
          rw [Category.assoc, hq]
      _ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]
      _ = q e ≫ thick R I e := hq e
      _ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]
  refine IsPullback.of_bot ?_ hcomm hbot
  rw [Category.comp_id, ← hq]
  exact (hβ e).2

end GlobalTheory.FormalAlg
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem GlobalTheory.FormalAlg.alg_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), Alg f I → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ j : ∀ e, (Y e).left ⟶ W, (∀ e, IsClosedImmersion (j e)) → (∀ e, j e ≫ f = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ j (e + 1) = j e) → ∃ (T : Scheme.{0}) (i : T ⟶ W) (c : ∀ e, (Y e).left ⟶ T), IsClosedImmersion i ∧ IsProper (i ≫ f) ∧ (∀ e, c e ≫ i = j e) ∧ ∀ e, IsPullback (c e) (Y e).hom (i ≫ f) (thick R I e) := by
  intro R _ I W f hA Y β hβ hY j hj hjf hβj
  have hP := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  have key : ∀ e (T : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i →
      ((∃ b : (Y e).left ⟶ T, b ≫ i = j e ∧ IsPullback b (Y e).hom (i ≫ f) (thick R I e)) ↔
        i.ker ⊔ baseIdeal f (I ^ (e + 1)) = (j e).ker) :=
    fun e T i hi => GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W T (Y e).left f i (j e) (Y e).hom hi (hj e) (hjf e)
  have hsys : IsSystem f I (fun e => (j e).ker) := by
    intro e
    exact ((key e _ (j (e + 1)) (hj (e + 1))).1 ⟨β e, hβj e, by rw [hjf (e + 1)]; exact hP e⟩).symm
  have hprop : ∀ e, IsProper ((j e).ker.subschemeι ≫ f) := by
    intro e
    have h0 : (j e).toImage ≫ ((j e).ker.subschemeι ≫ f) = (Y e).hom ≫ thick R I e := by
      rw [← hjf e, ← Category.assoc]
      exact congrArg (· ≫ f) (Scheme.Hom.toImage_imageι (j e))
    have h1 : (j e).ker.subschemeι ≫ f = inv (j e).toImage ≫ (Y e).hom ≫ thick R I e := by
      rw [← h0, IsIso.inv_hom_id_assoc]
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [h1]
    infer_instance
  obtain ⟨T, hTp, hTr⟩ := hA _ hsys hprop
  have hc : ∀ e, ∃ b : (Y e).left ⟶ T.subscheme, b ≫ T.subschemeι = j e ∧
      IsPullback b (Y e).hom (T.subschemeι ≫ f) (thick R I e) := fun e =>
    (key e _ T.subschemeι inferInstance).2 (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hTr e)
  choose c hc1 hc2 using hc
  exact ⟨T.subscheme, T.subschemeι, c, inferInstance, hTp, hc1, hc2⟩
end
