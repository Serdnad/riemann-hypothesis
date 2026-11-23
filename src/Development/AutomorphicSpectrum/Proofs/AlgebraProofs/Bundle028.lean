module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle006
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.padic_embedding_valuation_subring : ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]), ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_valuationSubring_of_padicEmbedding | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_valuationSubring_of_padicEmbedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_valuationSubring_of_padicEmbedding <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.RelDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq_field (H : Host E) : ((H.rt : E)) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at h
  exact h

theorem rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq_field H
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h1
  exact H.d_prime.ne_zero h1

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero] at hre him
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  rw [← map_pow, rt_sq_field, map_neg, map_natCast]
  simp

theorem exists_local_generator (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) :
    ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ],
      Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧
      Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  obtain ⟨δ₀, -, hδ₀, hconj, hlog⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hrt : (H.rt : E) ≠ 0 := rt_ne_zero H
  have hδ₀E : (δ₀ : E) ≠ 0 := by exact_mod_cast hδ₀
  refine ⟨(δ₀ : E) / (H.rt : E), div_ne_zero hδ₀E hrt, fun j => ⟨?_, ?_⟩⟩
  · rw [map_div₀, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hδ₀E))
        (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hrt)), hlog]
  · rw [map_div₀, hconj, conj_rt H, div_neg, map_neg, norm_neg]

end GlobalTheory.CompanionTheory.Ar.Fl.RelDiff
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂] (r r₂ : ℕ) (L : AddSubgroup E) (C C' : AddSubgroup E₂) (Δ : AddSubgroup (E × E₂)), LocFree R r L → LocFree R r₂ C → LocFree R r₂ C' → (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → (∀ v w, (v, w) ∈ Δ → v ∈ L ∧ w ∈ C) → (∀ v ∈ L, ∃ w, (v, w) ∈ Δ) → (∀ w, (0, w) ∈ Δ ↔ w ∈ C') → (∀ w ∈ C, ∃ v, (v, w) ∈ Δ) → LocFree R (r + r₂) Δ ∧ LocFree R r (Δ.comap (AddMonoidHom.inl E E₂)) := by
  intro o Ω _ _ _ R E E₂ _ _ _ _ r r₂ L C C' Δ hL hC hC' hsm hsub hliftL hker hliftC
  have hC'eq : AddSubgroup.comap (LinearMap.inr Ω E E₂).toAddMonoidHom Δ = C' := by
    ext w
    change (0, w) ∈ Δ ↔ w ∈ C'
    exact hker w
  have hLeq : AddSubgroup.map (LinearMap.fst Ω E E₂).toAddMonoidHom Δ = L := by
    ext v
    constructor
    · rintro ⟨⟨v', w⟩, h, rfl⟩
      exact (hsub v' w h).1
    · intro hv
      obtain ⟨w, hw⟩ := hliftL v hv
      exact ⟨(v, w), hw, rfl⟩
  have hCeq : AddSubgroup.map (LinearMap.snd Ω E E₂).toAddMonoidHom Δ = C := by
    ext w
    constructor
    · rintro ⟨⟨v, w'⟩, h, rfl⟩
      exact (hsub v w' h).2
    · intro hw
      obtain ⟨v, hv⟩ := hliftC w hw
      exact ⟨(v, w), hv, rfl⟩
  have hΔ : LocFree R (r + r₂) Δ := by
    have h := GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt.main R (LinearMap.inr Ω E E₂) (LinearMap.fst Ω E E₂)
      LinearMap.inr_injective LinearMap.fst_surjective
      (LinearMap.range_inr (R := Ω) (M := E) (M₂ := E₂)) Δ r₂ r hsm
      (by rw [hC'eq]; exact hC') (by rw [hLeq]; exact hL)
    rwa [Nat.add_comm] at h
  refine ⟨hΔ, ?_⟩
  have h := GlobalTheory.T.locally_free_of_short_exact R (LinearMap.inl Ω E E₂) (LinearMap.snd Ω E E₂)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl (R := Ω) (M := E) (M₂ := E₂)) Δ r r₂ hΔ (by rw [hCeq]; exact hC)
  have he : (LinearMap.inl Ω E E₂).toAddMonoidHom = AddMonoidHom.inl E E₂ := by
    ext x <;> simp
  rw [he] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  exact @PositivityTheory.Xgn.good_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange
end

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.locally_free_test_point_membership : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
open GlobalTheory.CompanionTheory.Ar.GR.SubGrp (exists_eq_spMap exists_sp_iso exists_grpObj_of_mono) in

theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme :
    ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
      (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A),
      IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  intro R _ A _ B _ _ h H
  have hmono : Mono h := by
    constructor
    intro T a b hab
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun k => ?_
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f k ≫ T.hom)
    let j : T' ⟶ T := Over.homMk (T.left.affineCover.f k) rfl
    have : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X k))
    obtain ⟨S, _, _, i, _⟩ := exists_sp_iso T'
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (i ≫ j ≫ a)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (i ≫ j ≫ b)
    have hφψ := H.mono S φ ψ (by simp only [← hφ, ← hψ, Category.assoc, hab])
    have hj : j ≫ a = j ≫ b := by rw [← cancel_epi i, hφ, hψ, hφψ]
    exact congrArg (·.left) hj
  have hmul : ∃ m : sp (R₀ := R) B ⊗ sp (R₀ := R) B ⟶ sp (R₀ := R) B,
      m ≫ h = (fst _ _ ≫ h) * (snd _ _ ≫ h) := by
    have : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
    have : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
      Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (sp (R₀ := R) B ⊗ sp (R₀ := R) B)
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ fst _ _)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (j ≫ snd _ _)
    obtain ⟨χ, hχ⟩ := H.mul S φ ψ
    refine ⟨inv j ≫ spMap χ, ?_⟩
    rw [Category.assoc, hχ, ← hφ, ← hψ, MonObj.comp_mul, Category.assoc, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  have hone : ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ sp (R₀ := R) B, e ≫ h = 1 := by
    have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (IsAffine (Spec _))
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (𝟙_ (Over (Spec (CommRingCat.of R))))
    obtain ⟨χ, hχ⟩ := H.one S
    exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩
  obtain ⟨i, hi⟩ := H.inv B (AlgHom.id R B)
  have hid : spMap (AlgHom.id R B) = 𝟙 (sp (R₀ := R) B) := by
    apply Over.OverMorphism.ext
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, Over.id_left]
    exact Spec.map_id _
  rw [hid, Category.id_comp] at hi
  obtain ⟨m, hm⟩ := hmul
  obtain ⟨e, he⟩ := hone
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e (spMap i) hm he hi
  exact ⟨G, hG, hmono⟩
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : TorsRep G p) (N : Type) [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → Finite N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite | exact GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.tors_pts_finite <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup | exact GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_eq_ev_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d),
    f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) :=
  PositivityTheory.HtPt.Cb.frob_subst

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem lin_comp_chain : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 :=
  @PositivityTheory.HtPt.Ca.lin_comp

end GlobalTheory.CompanionTheory.Ar.Conj
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg

theorem det_adapted {K V : Type} [Field K] [AddCommGroup V] [Module K V] (W : Submodule K V)
    {m n : ℕ} (bW cW : Module.Basis (Fin m) K W) (bQ cQ : Module.Basis (Fin n) K (V ⧸ W))
    (b c : Module.Basis (Fin (m + n)) K V)
    (hb1 : ∀ j, b (Fin.castAdd _ j) = bW j) (hb2 : ∀ j, W.mkQ (b (Fin.natAdd _ j)) = bQ j)
    (hc1 : ∀ j, c (Fin.castAdd _ j) = cW j) (hc2 : ∀ j, W.mkQ (c (Fin.natAdd _ j)) = cQ j) :
    b.det c = bW.det cW * bQ.det cQ := by
  have h1 : ∀ (i : Fin m) (x : W), b.repr (x : V) (Fin.castAdd _ i) = bW.repr x i := by
    intro i x
    have : (b.coord (Fin.castAdd _ i)).comp W.subtype = bW.coord i := by
      refine bW.ext fun j => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
        ← hb1, Module.Basis.repr_self, Finsupp.single_apply, Fin.castAdd_inj]
    exact LinearMap.congr_fun this x
  have h2 : ∀ (i : Fin n) (x : V), b.repr x (Fin.natAdd _ i) = bQ.repr (W.mkQ x) i := by
    intro i x
    have : b.coord (Fin.natAdd _ i) = (bQ.coord i).comp W.mkQ := by
      refine b.ext fun j => ?_
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have h0 : W.mkQ (b (Fin.castAdd n j)) = 0 := by
          rw [hb1]; simp
        have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [LinearMap.comp_apply, Module.Basis.coord_apply, h0, map_zero,
          Module.Basis.repr_self, Finsupp.single_apply, hne, if_false, Finsupp.coe_zero,
          Pi.zero_apply]
      · simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb2,
          Module.Basis.repr_self, Finsupp.single_apply, Fin.natAdd_inj]
    exact LinearMap.congr_fun this x
  have key : (b.toMatrix c).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (bW.toMatrix cW)
        (Matrix.of fun i j => b.repr (c (Fin.natAdd _ j)) (Fin.castAdd _ i)) 0
        (bQ.toMatrix cQ) := by
    ext (i | i) (j | j)
    · simp [Module.Basis.toMatrix_apply, hc1, h1]
    · simp [Module.Basis.toMatrix_apply]
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Module.Basis.toMatrix_apply, hc1, h2, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 (cW j).2]
      simp
    · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right,
        Module.Basis.toMatrix_apply, hc2, h2, Matrix.fromBlocks_apply₂₂]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_fromBlocks_zero₂₁]

theorem deg_eq_subDeg_add_deg_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V)
    (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  rcases isEmpty_or_nonempty C.I with hI | ⟨⟨i₀⟩⟩
  · simp [subDeg, deg, finsum_of_isEmpty]
  have hex := fun i => (hL.1 i).elim fun b hb => GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
  choose bW bQ b hb hbW hbQ h1 h2 using hex
  obtain ⟨hS, hQ⟩ := GlobalTheory.T.sub_and_quotient_bundles K C V L W hL
  obtain ⟨-, eL⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (b i₀) b hL hb
  obtain ⟨fS, eS⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C W (sub C L W) _ (bW i₀) bW hS hbW
  obtain ⟨fQ, eQ⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (V ⧸ W) (quot C L W) _ (bQ i₀) bQ hQ hbQ
  rw [subDeg, eL, eS, eQ, ← finsum_add_distrib]
  · refine finsum_congr fun i => ?_
    rw [det_adapted W (bW i₀) (bW i) (bQ i₀) (bQ i) (b i₀) (b i) (h1 i₀) (h2 i₀) (h1 i) (h2 i),
      map_mul, WithZero.log_mul, mul_add]
    · exact (C.v i).ne_zero_iff.2 ((bW i₀).isUnit_det (bW i)).ne_zero
    · exact (C.v i).ne_zero_iff.2 ((bQ i₀).isUnit_det (bQ i)).ne_zero
  · refine fS.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]
  · refine fQ.subset fun i hi h => hi ?_
    simp only [h, WithZero.log_one, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg
end
