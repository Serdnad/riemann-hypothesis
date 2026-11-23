module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle109
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle189
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle113
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle115
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem dictIsUnif_of_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  intro D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hK
  obtain ⟨h4, h5⟩ := GlobalTheory.T.memberDictionary_real_equivariant_onto_triangular D H Dw l Xo c σ V r C hC dict hd
  refine ⟨h1, h2, ⟨fun k => C.fr 1 k, fun k => ⟨(GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.1, hd.2 k⟩, h4⟩,
    h3, h5, ?_⟩
  rintro g g' ⟨δ, hδ, he⟩
  obtain ⟨γ, hγ, hf⟩ := hd.1 g
  obtain ⟨γ', hγ', hf'⟩ := hd.1 g'
  rw [he] at hγ' hf'
  dsimp only at hγ' hf'
  obtain ⟨γ₁, hγ₁, hm, hfr⟩ := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g _ γ hγ).2.2.2 δ hδ
  have hk := GlobalTheory.T.mem_levelK_of_same_mark_and_frame D H Dw l Xo c σ V r C hC Kf hK g g' _ _ _ hm hγ' (by rw [hfr, ← hf, hf'])
  refine ⟨γ'⁻¹ * (γ₁ * γ), mul_mem (inv_mem hγ'.1) hm.1, _, hk, ?_⟩
  group

end GlobalTheory.Member
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.cuspSection_adelic_leftInvariant_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  first | exact @GlobalTheory.Member.adel_leftInv_and_continuous | exact GlobalTheory.Member.adel_leftInv_and_continuous | (intros; apply GlobalTheory.Member.adel_leftInv_and_continuous <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat


open ConjIsometry in
theorem exists_isometry_of_conj_split_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    GlobalTheory.T.exists_lattice_linearMap_conjugate_splitPoint E H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add (f := _), LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_isometry_of_conjugate_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  first | exact @GlobalTheory.CompRat.exists_isometry_of_conj_split | exact GlobalTheory.CompRat.exists_isometry_of_conj_split | (intros; apply GlobalTheory.CompRat.exists_isometry_of_conj_split <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.FrameNorm
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem congr_of_dvd_modulus {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    (Λ : Submodule (𝓞 E) (Fin r → E)) (φ : L ≃ₗ[𝓞 E] Λ) (γ : Matrix (Fin r) (Fin r) E) {m N : ℕ} (hd : m ∣ N)
    (h : ∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec γ x - x = (N : E) • y) (a : L) :
    ∃ b : L, γ.mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + m • (φ b : Fin r → E) := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨y, hy, e⟩ := h _ (φ a).2
  refine ⟨φ.symm (d • ⟨y, hy⟩), ?_⟩
  rw [LinearEquiv.apply_symm_apply, ← sub_eq_iff_eq_add', e, Nat.cast_smul_eq_nsmul, mul_smul]
  rfl

theorem exists_unf_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Formalism.L2.PjFree.Unf Xo c σ r, Formalism.L2.PjFree.IsUnf U ∧ HasPrinc U l.M' ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  have hN : N1c := GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws
  have hH := GlobalTheory.T.hasse_norm_theorem_quadratic_extension
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, fun k γ hγ h => ?_,
    ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨GlobalTheory.T.arithmeticGroup_cuspCentre_lattice E r ρ _ _, fun hA => ?_⟩⟩
  · exact (hM.gam k γ).2 ⟨hγ, fun a _ => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_left _ _) h a,
      fun a => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_right _ _) h a⟩
  · exact GlobalTheory.T.flagDomainModels_exponents_levelM E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_unf_of_space : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Formalism.L2.PjFree.Unf Xo c σ r, Formalism.L2.PjFree.IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro hN hH hB hT E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨GlobalTheory.T.arithmeticGroup_cuspCentre_lattice E r ρ _ _, fun hA => ?_⟩⟩
  exact GlobalTheory.T.flagDomainModels_exponents_levelM E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
end
