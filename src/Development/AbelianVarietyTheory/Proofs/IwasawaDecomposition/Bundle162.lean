module

import Formalism.SharpRestriction.LevelLetterCocycles.Bundle027
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle157
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle155
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem finiteDimensional_Ks_of_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  apply Formalism.MainNotions.WachCoordinates.Br.fd_Ks <;> assumption

end GlobalTheory.MemLoc
end

section

noncomputable section

namespace GlobalTheory.Mem.UnitaryEmb

open scoped TensorProduct
open NumberField Matrix

section General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (B A : HSpace E) (ι : B.V →ₗ[E] A.V) (h : HSpace.IsIsomEmb B A ι)

theorem continuous_embA : Continuous (embA hc B A ι h) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine Continuous.subtype_mk (Continuous.comp (g := Units.map _) ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const))

theorem embA_ratA (γ : GRat hc B) : embA hc B A ι h (ratA hc B γ) = ratA hc A (embRat hc B A ι h γ) := by
  refine Subtype.ext (Units.ext ?_)
  show 1 + (embMat B A ι).map (inclR (F := F) (AF F)) *
      (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E).map (inclR (F := F) (AF F)) - 1) *
        (projMat hc B A ι).map (inclR (F := F) (AF F)) =
    (1 + embMat B A ι * (((γ : GL (Fin B.rank) E) : Matrix (Fin B.rank) (Fin B.rank) E) - 1) *
      projMat hc B A ι).map (inclR (F := F) (AF F))
  rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_embHom (D : D7) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (hι : HSpace.IsIsomEmb B A ι) :
    ∃ s : GA D B →* GA D A, Continuous s ∧ (∀ h g, EmbRel A B ι g h ↔ g = s h) ∧ ∀ γ ∈ GQ B, s γ ∈ GQ A := by
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι, continuous_embA D.sp.cm B A ι hι,
    fun h g => GlobalTheory.AutFunCompare.embRel_iff A B ι hι g h, ?_⟩
  rw [GlobalTheory.AutFunCompare.GQ_eq, GlobalTheory.AutFunCompare.GQ_eq]
  rintro _ ⟨γ, rfl⟩
  exact ⟨_, (embA_ratA D.sp.cm B A ι hι γ).symm⟩

end GlobalTheory.Mem.UnitaryEmb

end
end

section

open Matrix

theorem _root_.GlobalTheory.T.quadraticGelfandInvariant_eq_neg_sum_sq_definite : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  first | exact @GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq | exact GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq | (intros; apply GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_weil_of_fixes' : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (h' : IsPlaceOver A W) (σ : Weil h), (∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x) → ∃ τ : Weil h', ∀ z : Ω, (σ : G E Ω) z = (τ : G K Ω) z := by
  first | exact @GlobalTheory.WeilSurj.exists_weil_of_fixes | exact GlobalTheory.WeilSurj.exists_weil_of_fixes | (intros; apply GlobalTheory.WeilSurj.exists_weil_of_fixes <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLogTheta

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem eigen_add (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c d : G → R) (t : R) (ht : t ≠ 0)
    (hθt : θ t = 0) (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * (y + d g * t ^ (n + 1))) →
      ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w + d g * t := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow, map_add (f := _), map_mul, map_pow, hθt,
        zero_pow (Nat.succ_ne_zero _), mul_zero, add_zero]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_form (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.BdR l) (d : GQ l → Per.BdRp l)
    (hb : ∀ g : GQ l, Per.σD g b = b + algebraMap (Per.BdRp l) (Per.BdR l) (d g * C.j C.t)) :
    ∃ (a : ℚ_[l]) (v : Per.BdRp l), b = algebraMap (Per.BdRp l) (Per.BdR l)
      (C.o (algebraMap ℚ_[l] (Om l) a) + C.j C.t * v) := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C (botExt l)
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l (botExt l)
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  let c : GQ l → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : GQ l, Per.σDp g t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, InvDR.j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hθt : Per.θD l t = 0 := (hker t).2 ht1
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : GQ l, Per.σC g x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g _ => by simpa only [hθc] using h g
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : GQ l, Per.σDp g y = c g ^ n * (y + d g * t ^ (n + 1)) := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g]
    simp only [map_mul, map_pow, map_add (f := _)]
    rw [← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_add (Per.θD l) (fun g : GQ l => Per.σDp g) (fun g => Per.σC g) c d t ht0
    hθt hker' hc (fun g y => hθ g y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g _ => by
    rw [← hθ, hw' g, map_add (f := _), map_mul, hθt, mul_zero, add_zero]
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hk
  obtain ⟨v, hv⟩ := hker' (w - C.o (algebraMap ℚ_[l] (Om l) a))
    (by rw [map_sub, C.o_sec.th, hkθ, sub_self])
  refine ⟨a, v, ?_⟩
  rw [← hv, add_sub_cancel]
  have : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (b : P.R.B) (c : GQ l → ℚ_[l]), (∀ g : GQ l, P.actQ g b - b = c g • P.tB) →
    ∃ a : ℚ_[l], P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) ∈ (P.PD (botExt l)).Fil 0 := by
  intro l _ P AI T b c hb
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have hι : ∀ g : GQ l, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun g => by
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at this
    exact this.symm
  have ht : T.eD (P.ιB P.tB) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) := by
    rw [hC.ι, hC.t, Core.tB, C.ι_j]
  have hq : ∀ a : ℚ_[l], T.eD (P.ιB (algebraMap ℚ_[l] P.R.B a)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (algebraMap ℚ_[l] (Om l) a)) := fun a => by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hC.o]
    rfl
  obtain ⟨a, v, h⟩ := core_form l C (T.eD (P.ιB b)) (fun g => C.o (algebraMap ℚ_[l] (Om l) (c g))) fun g => by
    rw [← T.actD, hι, map_mul, ← hq, ← ht, ← map_mul, ← map_mul, ← map_add (f := _), ← map_add (f := _), ← Algebra.smul_def,
      ← hb, add_sub_cancel]
  refine ⟨a, ?_⟩
  have h1 : T.eD (P.ιB (tInv P)) * algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) = 1 := by
    rw [← ht, ← map_mul, ← map_mul, tInv_mul, map_one, map_one]
  have h2 : T.eD (P.ιB ((b - algebraMap ℚ_[l] P.R.B a) * tInv P)) =
      algebraMap (Per.BdRp l) (Per.BdR l) v := by
    rw [map_mul, map_mul, map_sub, map_sub, hq, h, map_add (f := _), map_mul]
    linear_combination algebraMap (Per.BdRp l) (Per.BdR l) v * h1
  rw [T.fil, h2]
  have h3 : (1 : Per.BdR l) ∈ Per.FilD l 0 := by
    have := (T.fil (botExt l) 0 1).1 (P.PD (botExt l)).one_mem
    rwa [map_one] at this
  have h4 := (Per.FilD l 0).smul_mem v h3
  rwa [Algebra.smul_def, mul_one] at h4

end GlobalTheory.Pst.NoLogTheta
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstDescent

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier

theorem exists_fnOf_eq_of_algebraic {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp F) (U : X.Opens) (hU : genericPoint X ∈ U)
    {a : X.functionField} (ha : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (Cartier.constFn p) a = 0) :
    ∃ s : Γ(X, U), fnOf U hU s = a := by
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI := (algX p U).toAlgebra
  letI : Algebra F X.functionField := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower F Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U hU).symm
  obtain ⟨P, hP, hPa⟩ := ha
  have hint : IsIntegral F a := (show IsAlgebraic F a from
    ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩).isIntegral
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(X, U))
    (A := X.functionField)).1 hint.tower_top
  exact ⟨s, hs⟩

theorem appLE_comp_algX {F : Type} [CommRing F] {W V : Scheme.{0}} (pW : W ⟶ Sp F) (π : V ⟶ W) :
    (π.appLE ⊤ ⊤ le_top).hom.comp (algX pW ⊤) = algX (π ≫ pW) ⊤ := by
  have e := Scheme.Hom.appLE_comp_appLE π pW ⊤ ⊤ ⊤ le_top le_top
  exact congrArg (fun f => (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom) e

theorem descent : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V]
    [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV →
    (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) →
      b ∈ (GlobalTheory.Cartier.constFn pV).range) →
    ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  intro F _ W V _ _ _ pW pV π hπ hV a ha
  subst hπ
  have hW : genericPoint W ∈ (⊤ : W.Opens) := trivial
  have hV' : genericPoint V ∈ (⊤ : V.Opens) := trivial

  let φ : Γ(W, ⊤) →+* V.functionField := (fnOf ⊤ hV').comp (π.appLE ⊤ ⊤ le_top).hom
  have hφ : φ.comp (algX pW ⊤) = Cartier.constFn (π ≫ pW) := by
    simp only [φ, RingHom.comp_assoc, appLE_comp_algX]
    rfl
  obtain ⟨s, hs⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW ha
  obtain ⟨P, hP, hPa⟩ := ha
  have h0 : P.eval₂ (algX pW ⊤) s = 0 := fnOf_injective ⊤ trivial (by
    rw [Polynomial.hom_eval₂, fnOf_comp_algX pW ⊤ hW, hs, hPa, map_zero])
  have hb : P.eval₂ (Cartier.constFn (π ≫ pW)) (φ s) = 0 := by
    rw [← hφ, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c, hc⟩ := hV _ ⟨P, hP, hb⟩
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : a - Cartier.constFn pW c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht : fnOf ⊤ hW (s - algX pW ⊤ c) = a - Cartier.constFn pW c := by
    rw [map_sub, hs, ← fnOf_comp_algX pW ⊤ hW, RingHom.comp_apply]
  have hφt : φ (s - algX pW ⊤ c) = 0 := by
    rw [map_sub, ← RingHom.comp_apply φ, hφ, hc, sub_self]
  have hinv : ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.eval₂ (Cartier.constFn pW) (a - Cartier.constFn pW c)⁻¹ = 0 := by
    letI : Algebra F W.functionField := (Cartier.constFn pW).toAlgebra
    have h1 : IsAlgebraic F a :=
      ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩
    have h2 : IsAlgebraic F (a - Cartier.constFn pW c) :=
      h1.sub (isAlgebraic_algebraMap (A := W.functionField) c)
    obtain ⟨Q, hQ, hQx⟩ := h2.inv
    exact ⟨Q, hQ, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at hQx; exact hQx⟩
  obtain ⟨u, hu⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW hinv
  have htu : (s - algX pW ⊤ c) * u = 1 := fnOf_injective ⊤ trivial (by
    rw [map_mul, ht, hu, map_one, mul_inv_cancel₀ hne'])
  have h3 := congrArg φ htu
  rw [map_mul, hφt, zero_mul, map_one] at h3
  exact zero_ne_one h3

end GlobalTheory.ConstDescent
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomIntConst

theorem finrank_eq_one_of_isDomain_tensor {F L : Type} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsDomain (L ⊗[F] L)] : Module.finrank F L = 1 := by
  have hinj : Function.Injective (algebraMap L (L ⊗[F] L)) := (algebraMap L (L ⊗[F] L)).injective
  have hT : IsField (L ⊗[F] L) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField L)
  let f : L ⊗[F] L →ₐ[L] L := Algebra.TensorProduct.lmul'' F
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    obtain ⟨y, hy⟩ := hT.mul_inv_cancel h
    have := congrArg f hy
    rw [map_mul, hx, zero_mul, map_one] at this
    exact zero_ne_one this
  have hs : Function.Surjective f := fun x => ⟨x ⊗ₜ 1, by
    show Algebra.TensorProduct.lmul'' F (x ⊗ₜ[F] (1 : L)) = x
    first
      | simp [Algebra.TensorProduct.lmul''_apply_tmul]
      | exact (Algebra.TensorProduct.lmul'_apply_tmul (R := F) x (1 : L)).trans (mul_one x)⟩
  have e := (LinearEquiv.ofBijective f.toLinearMap ⟨hf, hs⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_self] at e
  exact e

theorem mem_range_constFn (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    [GeometricallyIntegral p] (b : Y.functionField)
    (hb : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) b = 0) :
    b ∈ (GlobalTheory.Cartier.constFn p).range := by
  letI : Algebra F Y.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  obtain ⟨P, hP, hPb⟩ := hb
  have hint : IsIntegral F b := (show IsAlgebraic F b from ⟨P, hP, hPb⟩).isIntegral
  obtain ⟨V, hV, s₀, hs₀⟩ := Y.presheaf.exists_germ_eq b
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let s : Γ(Y, U) := resG Y hUV s₀
  have hs : GlobalTheory.Cartier.fnOf U hxU s = b := by
    rw [GlobalTheory.Cartier.fnOf_resG]; exact hs₀
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have e : (GlobalTheory.Cartier.fnOf U hxU).comp (algebraMap F Γ(Y, U)) = algebraMap F Y.functionField :=
    GlobalTheory.Cartier.fnOf_comp_algX p U hxU
  have hm : Polynomial.aeval s (minpoly F b) = 0 := by
    apply GlobalTheory.Cartier.fnOf_injective U hxU
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, e, hs, ← Polynomial.aeval_def,
      minpoly.aeval]
  haveI : Fact (Irreducible (minpoly F b)) := ⟨minpoly.irreducible hint⟩
  let φ : AdjoinRoot (minpoly F b) →ₐ[F] Γ(Y, U) := AdjoinRoot.liftAlgHom (minpoly F b) (Algebra.ofId F Γ(Y, U)) s
    (by rw [Polynomial.aeval_def] at hm; exact hm)
  have hφ : Function.Injective φ := φ.toRingHom.injective

  let g := Spec.map (CommRingCat.ofHom (algebraMap F (AdjoinRoot (minpoly F b))))
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hYL : IsIntegral (pullback p g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback p g)
  have : Surjective g := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : Nonempty ((pullback hU.fromSpec (pullback.fst p g) : Scheme.{0})) := by
    obtain ⟨z, -⟩ : genericPoint Y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have hz : z ∈ Set.range (pullback.fst hU.fromSpec (pullback.fst p g)) := by
      rw [Scheme.Pullback.range_fst]; exact (pullback.fst p g).surjective _
    exact ⟨hz.choose⟩
  haveI := hU.isOpenImmersion_fromSpec
  have : IsIntegral (pullback hU.fromSpec (pullback.fst p g)) :=
    isIntegral_of_isOpenImmersion (pullback.snd hU.fromSpec (pullback.fst p g))
  have : IsIntegral (pullback (hU.fromSpec ≫ p) g) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p g hU.fromSpec).hom
  rw [hg] at this
  have : IsIntegral (Spec (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))) :=
    IsIntegral.of_isIso (pullbackSpecIso F Γ(Y, U) (AdjoinRoot (minpoly F b))).hom
  have : IsDomain (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)) :=
    (affine_isIntegral_iff (.of (Γ(Y, U) ⊗[F] AdjoinRoot (minpoly F b)))).mp this

  have hinj : Function.Injective (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := AdjoinRoot (minpoly F b))
      φ.toLinearMap hφ
  have : IsDomain (AdjoinRoot (minpoly F b) ⊗[F] AdjoinRoot (minpoly F b)) :=
    Function.Injective.isDomain (Algebra.TensorProduct.map φ
      (AlgHom.id F (AdjoinRoot (minpoly F b)))).toRingHom hinj
  have hm0 : minpoly F b ≠ 0 := minpoly.ne_zero hint
  have : FiniteDimensional F (AdjoinRoot (minpoly F b)) := (AdjoinRoot.powerBasis hm0).finite
  have h1 := finrank_eq_one_of_isDomain_tensor (F := F) (L := AdjoinRoot (minpoly F b))
  rw [(AdjoinRoot.powerBasis hm0).finrank, AdjoinRoot.powerBasis_dim] at h1
  exact minpoly.natDegree_eq_one_iff.1 h1

end GlobalTheory.GeomIntConst
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0}) [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules) {ι : Type} [Fintype ι] (L : ι → LB Z), interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  first | exact @GlobalTheory.GroundFieldChange.interNum_fieldChange | exact GlobalTheory.GroundFieldChange.interNum_fieldChange | (intros; apply GlobalTheory.GroundFieldChange.interNum_fieldChange <;> assumption)
end
