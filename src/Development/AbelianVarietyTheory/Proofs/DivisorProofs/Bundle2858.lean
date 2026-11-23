module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfFiniteProjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem isFrame_chart (h : IsGrpPullback H G x ψ) (j : PUnit → (hodge G g).ι) :
    IsFrame fun i => (omegaBase h).app (LB.wchart (hodge G g) (fun _ => x) j)
      (pullbackSections x (omega G) (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit) ((j PUnit.unit).e i)) :=
  (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame _).map_iso (omegaBase h)

def gen (h : IsGrpPullback H G x ψ) {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) : LB.Gen ((hodge G g).pull x) where
  s j := (isFrame_chart h j).detUnit ha le_rfl le_top

end GlobalTheory.HodgeFrameGen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.lbIso_detOm_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)),
    (GlobalTheory.FlagMod.detOm Y).IsLB →
      LBIso (GlobalTheory.FlagMod.detOm Y) (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) := by
  intro E _ _ _ H Dw l Xo c Y hO
  exact GlobalTheory.HodgeCech.lbIso_detOm_det Y hO (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

theorem zeta_pow_div_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : zeta N ^ (N / n) = zeta n := by
  obtain ⟨c, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hN
  have hc : c ≠ 0 := right_ne_zero_of_mul hN
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem cycAway_le_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : cycAway n ≤ cycAway N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow_div_of_dvd hN h]
    exact pow_mem (zetaAway N).2 _
  · obtain ⟨c, rfl⟩ := h
    have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)
    have e : (n : ℂ)⁻¹ = (c : ℂ) * ((n * c : ℕ) : ℂ)⁻¹ := by
      push_cast
      field_simp
    rw [e]
    exact mul_mem (natCast_mem _ _) (Subring.subset_closure (Or.inr rfl))

theorem zetaAway_pow_self {N : ℕ} (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

theorem formallyUnramified_cycAway {N : ℕ} (hN : N ≠ 0) (R : Type) [CommRing R] [Algebra R (cycAway N)] :
    Algebra.FormallyUnramified R (cycAway N) := by
  have hD : ∀ x : cycAway N, KaehlerDifferential.D R (cycAway N) x = 0 := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have h := congrArg (KaehlerDifferential.D R (cycAway N)) (zetaAway_pow_self hN)
        rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (cycAway N), smul_smul] at h
        have hu : IsUnit ((N : cycAway N) * zetaAway N ^ (N - 1)) :=
          (isUnit_natCast hN).mul ((IsUnit.of_pow_eq_one (zetaAway_pow_self hN) hN).pow _)
        exact hu.smul_eq_zero.1 h
      · let v : cycAway N := ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
        have hv : (N : cycAway N) * v = 1 :=
          Subtype.ext (by simpa [v] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0))
        have h := congrArg (KaehlerDifferential.D R (cycAway N)) hv
        rw [Derivation.leibniz, Derivation.map_one_eq_zero, Derivation.map_natCast, smul_zero, add_zero] at h
        exact (isUnit_natCast hN).smul_eq_zero.1 h
    | zero => exact map_zero _
    | one => exact Derivation.map_one_eq_zero _
    | add x y hx' hy' hx hy =>
      have := map_add (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, add_zero] at this
      exact this
    | neg x hx' hx =>
      have := map_neg (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩
      rw [hx, neg_zero] at this
      exact this
    | mul x y hx' hy' hx hy =>
      have := (KaehlerDifferential.D R (cycAway N)).leibniz ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩
  have hω : ω ∈ Submodule.span (cycAway N) (Set.range (KaehlerDifferential.D R (cycAway N))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine (Submodule.mem_bot (cycAway N)).1 (Submodule.span_le.2 ?_ hω)
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot (cycAway N)).2 (hD x)

theorem isIntegral_inclusion_cycAway {n N a : ℕ} (hN : N ≠ 0) (h : n ∣ N) (ha : N ∣ n ^ a) :
    (Subring.inclusion (cycAway_le_of_dvd hN h)).IsIntegral := by
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hN, by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
        exact sub_eq_zero.2 (zetaAway_pow_self hN)⟩
    · obtain ⟨c, hc⟩ := ha
      let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
      have hc' : (n : ℂ) ^ a = N * c := by exact_mod_cast hc
      convert RingHom.isIntegralElem_map (Subring.inclusion (cycAway_le_of_dvd hN h)) (x := (c : cycAway n) * v ^ a)
      refine Subtype.ext ?_
      change (N : ℂ)⁻¹ = (c : ℂ) * ((n : ℂ)⁻¹) ^ a
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← _root_.mul_assoc, ← hc', ← mul_pow, mul_inv_cancel₀ hn', one_pow]
  | zero => exact RingHom.isIntegralElem_zero _
  | one => exact RingHom.isIntegralElem_one _
  | add x y _ _ hx hy => exact hx.add _ hy
  | neg x _ hx => exact hx.neg _
  | mul x y _ _ hx hy => exact hx.mul _ hy

theorem exists_inclusion_cycAway : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧
    j (zetaAway n) = zetaAway N ^ (N / n) ∧
    ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  intro n N hN h
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  let j := Subring.inclusion (cycAway_le_of_dvd hN h)
  have hj : Function.Injective j := Subring.inclusion_injective _
  refine ⟨j, hj, Subtype.ext (zeta_pow_div_of_dvd hN h).symm, fun ⟨a, ha⟩ => ?_⟩
  have hint : j.IsIntegral := isIntegral_inclusion_cycAway hN h ha
  letI := j.toAlgebra
  have : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn).1
  have : Algebra.IsIntegral (cycAway n) (cycAway N) := ⟨hint⟩
  have := finiteType_cycAway N
  have : Algebra.FiniteType (cycAway n) (cycAway N) := .of_restrictScalars_finiteType ℤ _ _
  have hfin : Module.Finite (cycAway n) (cycAway N) := Algebra.IsIntegral.finite
  have : FaithfulSMul (cycAway n) (cycAway N) := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  have : Module.Flat (cycAway n) (cycAway N) := inferInstance
  have : Algebra.FinitePresentation (cycAway n) (cycAway N) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have := formallyUnramified_cycAway hN (cycAway n)
  have het : Algebra.Etale (cycAway n) (cycAway N) := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨(IsFinite.SpecMap_iff _).2 hfin, HasRingHomProperty.Spec_iff.2 het, ⟨?_⟩⟩
  exact hint.comap_surjective hj

end GlobalTheory.SiegelTor
end

section

open GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
  ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  first | (exact @GlobalTheory.CycLift.exists_hom_to_field) | (exact GlobalTheory.CycLift.exists_hom_to_field) | (intros; apply GlobalTheory.CycLift.exists_hom_to_field  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  first | exact @GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | exact GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | (intros; apply GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isRadical_span_prod_relativeRegularParameters : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R) (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  first | exact @GlobalTheory.RelParamRad.isRadical_span_prod | exact GlobalTheory.RelParamRad.isRadical_span_prod | (intros; apply GlobalTheory.RelParamRad.isRadical_span_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.symmetric_bundle_level_odd : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (β₀ : cycAway M →+* k) (z₀ : kˣ), x₀ ≫ t = spMap β₀ → (z₀ : k) = β₀ (zetaAway M) → (∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x₀) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z₀ ^ (2 * omegaStd a b)))) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S) (β : cycAway M →+* k') (z : k'ˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k') = β (zetaAway M) → ∀ a b, Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.WeilOpenLocus.weil_open) | (exact GlobalTheory.WeilOpenLocus.weil_open) | (intros; apply GlobalTheory.WeilOpenLocus.weil_open  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | exact GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_deRham_locallyFree_hodgeDegenerates : GlobalTheory.Published.AbelianHodgeDeRham := by
  first | exact @GlobalTheory.AbCoh.abelianHodgeDeRham | exact GlobalTheory.AbCoh.abelianHodgeDeRham | (intros; apply GlobalTheory.AbCoh.abelianHodgeDeRham <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  first | exact @GlobalTheory.KSFam.ksFamily | exact GlobalTheory.KSFam.ksFamily | (intros; apply GlobalTheory.KSFam.ksFamily <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefOfGen

theorem card_pos_of_isAlgPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) : (0 : ℝ) < Nat.card (X.residueField x →+* ℂ) := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have := GlobalTheory.SmallSecHeight.numberField hZ hc'
  rw [GlobalTheory.HtSelfInter.card_ringHom_eq]
  exact_mod_cast Nat.card_pos

theorem nef_of_gen : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hA k _ X _ p D hX M m N s hm hs hsp hf
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((M.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => GlobalTheory.AmpleHtLow.small_of_shift k X p D hX M m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 M
  refine ⟨-(-(∑ i, |c i|)), ?_, GlobalTheory.HtSelfInter.isNef_shift hX hsp hf fun x hx => ?_⟩
  · rw [neg_neg]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  obtain ⟨i, hi⟩ := hs x hx.1
  have hN := card_pos_of_isAlgPt hX hx
  have hb : IsPtHt M x (h x / Nat.card (X.residueField x →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  refine ⟨_, hb, ?_⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt k X p D hX M m (c i) _ x (s i) hm (hc i) hi hx hb
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  exact h2.trans h1

end GlobalTheory.NefOfGen

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefTens

theorem isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  intro HC k _ X _ p D hX L M NL NM
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  refine ⟨NL.semiPos.tens NM.semiPos, ?_, fun Z i _ _ _ hc hd => ?_⟩
  · intro Z i _ _ κ _ _ _ hd
    rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
    exact add_nonneg (NL.vertical Z i κ hd) (NM.vertical Z i κ hd)
  · obtain ⟨h, H⟩ := hex L
    obtain ⟨h', H'⟩ := hex M
    obtain ⟨h'', H''⟩ := hex (L.tens M)
    obtain ⟨r, hr⟩ := exists_isRatSec ((L.tens M).restr i).isLB
    obtain ⟨r₁, hr₁, h1⟩ := NL.horizontal Z i hc hd
    obtain ⟨r₂, hr₂, h2⟩ := NM.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H''.point Z i hc hd r hr,
      PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd),
      H.point Z i hc hd r₁ hr₁, H'.point Z i hc hd r₂ hr₂]
    exact add_nonneg h1 h2

end GlobalTheory.NefTens
end
end
