module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle875
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DefU.CoefSp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def coef (W : GlobalTheory.DefU.Wt E n) : Module.Dual ℂ (Module.End ℂ W.Sp) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (W.rep x)

def C (W : GlobalTheory.DefU.Wt E n) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef W)

instance (W : GlobalTheory.DefU.Wt E n) : FiniteDimensional ℂ (C W) := LinearMap.finiteDimensional_range _

theorem C_right (W : GlobalTheory.DefU.Wt E n) {c : infU E n → ℂ} (hc : c ∈ C W) (y : infU E n) :
    (fun x => c (x * y)) ∈ C W := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (W.rep y), funext fun x => ?_⟩
  change B (W.rep x * W.rep y) = B (W.rep (x * y))
  exact congrArg B (map_mul W.rep x y).symm

def Y (W : GlobalTheory.DefU.Wt E n) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C W).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {W : GlobalTheory.DefU.Wt E n} {ψ : UA E n → ℂ} :
    ψ ∈ Y W ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C W := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : GlobalTheory.DefU.AutSub E n) (W : GlobalTheory.DefU.Wt E n) (hW : π.finPart W ≠ ⊥) : π.V ≤ Y W := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (Subtype.ext (LinearMap.ext h))
  have hvπ : f.1 v ∈ π.V := GlobalTheory.DefU.AutSub.mem_finPart.1 hf v
  have hvY : f.1 v ∈ Y W := mem_Y.2 fun g =>
    ⟨(LinearMap.proj g ∘ₗ f.1) ∘ₗ LinearMap.applyₗ v, funext fun x => by
      change f.1 (W.rep x v) g = f.1 v (g * x)
      rw [f.2.2 x v]
      rfl⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y W, RU E n x ψ ∈ π.V ⊓ Y W := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.DefU.admitted.exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) =
        fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [GlobalTheory.DefU.RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g,
        ← GlobalTheory.DefU.fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right W (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y W) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hvπ, hvY⟩ : f.1 v ∈ π.V ⊓ Y W))) hv
  · rw [← h]
    exact inf_le_right

theorem wt_eq (U : GlobalTheory.DefU.AutSub E n) (lam : GlobalTheory.DefU.Wt E n)
    (hw : ∀ v : InfinitePlace E, HasWeightAt U.V v.embedding (lam v)) : (GlobalTheory.DefU.AU.mk U).wt = lam := by
  funext v
  have h := GlobalTheory.DefU.AU.HasWt.wt ((GlobalTheory.DefU.AU.hasWt_mk U v.embedding (lam v)).2 (hw v))
  rw [GlobalTheory.DefU.Wt.at_embedding] at h
  exact GlobalTheory.DefU.hasWeightAt_unique U v.embedding ((GlobalTheory.DefU.AU.hasWt_mk U _ _).1 h) (hw v)

theorem coef_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n),
    ∃ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C ∧ ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ φ ∈ π, ∀ g : UA E n,
        (fun x : infU E n => φ (g * (x : UA E n))) ∈ C := by
  intro E _ _ _ n lam
  refine ⟨C lam, inferInstance, fun π hπ hw φ hφ g => ?_⟩
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have hne := GlobalTheory.DefU.AutSub.finPart_wt_ne_bot E n U
  rw [wt_eq U lam hw] at hne
  exact mem_Y.1 (le_Y U lam hne hφ) g

end GlobalTheory.DefU.CoefSp

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_exp_unique : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) P (y : Sp ℂ ⟶ F.X) e e', 3 ≤ N → FullMark N D' t → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D' t P y e' → e = e' := by
  intro O _ bar g ρ R _ σ Λ F N D' t P y e e' hN hfull hu hu'
  obtain ⟨w, h, ⟨hiso, hmark⟩, hPw, he⟩ :=
    GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ R σ Λ F N D' D' t t P P y e e' (by omega) hu hu'
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hu.2.1
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add (f := _), map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  have hid : hR = LinearMap.id := LinearMap.ext_on_range hspan fun a => by
    show h (P a) = P a
    rw [← hPw, ← hσ, key]
    rfl
  funext z
  have hz : h z = z := LinearMap.congr_fun hid z
  rw [← he z, hz]

end GlobalTheory.PELU
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structure_cohomology_residue_field_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  first | exact @GlobalTheory.AbCoh.CohBaseChange.main | exact GlobalTheory.AbCoh.CohBaseChange.main | (intros; apply GlobalTheory.AbCoh.CohBaseChange.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (n : ℕ) (u v : Fin n → GlobForm A.hom), wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) = wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) + wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) → wsum (OAff A.hom) u v = 0 := by
  first | exact @GlobalTheory.AbCoh.wsum_eq_zero_of_mul | exact GlobalTheory.AbCoh.wsum_eq_zero_of_mul | (intros; apply GlobalTheory.AbCoh.wsum_eq_zero_of_mul <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.wedge_property_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  first | exact @GlobalTheory.AbCoh.wedgeO_descends_field | exact GlobalTheory.AbCoh.wedgeO_descends_field | (intros; apply GlobalTheory.AbCoh.wedgeO_descends_field <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitive_axes_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → (NoPrimitiveStructureSheafH2 B → NoPrimitiveStructureSheafH2 A) ∧ (AxesVanishingStructureSheafDegOne B → AxesVanishingStructureSheafDegOne A) := by
  first | exact @GlobalTheory.AbCoh.noPrimO2_axesO1_descend | exact GlobalTheory.AbCoh.noPrimO2_axesO1_descend | (intros; apply GlobalTheory.AbCoh.noPrimO2_axesO1_descend <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonne_integrality_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  first | exact @GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful | exact GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful | (intros; apply GlobalTheory.Dieu.Integrality.exists_pow_smul_and_faithful <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section Helpers
variable {S : Scheme.{0}} {A : Over S}

theorem same_of_same_of_same {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) {y : Y ⟶ T} {u₁ u₂ : Y ⟶ U} (h₁ : Same A N M y u₁) (h₂ : Same A N M y u₂) :
    Same A M M u₁ u₂ := by
  rw [same_iff hN hM] at h₁ h₂
  rw [same_iff hM hM, ← h₁, h₂]

theorem same_ev_param_iff {T U P Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) (g : P ⟶ T) (h : P ⟶ U) (w : Y ⟶ P) :
    Same A (ev N (fst A P) (snd A P ≫ g)) (ev M (fst A P) (snd A P ≫ h)) w w ↔ Same A N M (w ≫ g) (w ≫ h) := by
  rw [same_iff (pull_isLB hN _) (pull_isLB hM _), same_iff hN hM, evc_ev hN, evc_ev hM]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

variable [GrpObj A]

theorem Fam.ev_param {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (g : P ⟶ T) :
    Fam A (_root_.GlobalTheory.AbDual.ev N (fst A P) (snd A P ≫ g)) := by
  refine ⟨pull_isLB hN.isLB _, (isAdditive_iff (pull_isLB hN.isLB _)).2 fun Y a a' t ↦ ?_⟩
  rw [evc_ev hN.isLB, evc_ev hN.isLB, evc_ev hN.isLB]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (t ≫ g)

end Helpers

theorem chartAt_of_lifting : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M → Inj A M → (∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f) → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u) → ChartAt A M N := by
  intro R _ _ A _ hA U M hU hM hInj crit T _ hT N hN hlift
  haveI : LocallyOfFiniteType T.hom := hT
  haveI : LocallyOfFiniteType U.hom := hU
  haveI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  haveI : LocallyOfFiniteType (T ⊗ U).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom ≫ T.hom))
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (T ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (T ⊗ U) hA _ _ (hN.ev_param (fst T U)) (hM.ev_param (snd T U))
  have key : ∀ (Y : Over (Sp R)) (w : Y ⟶ T ⊗ U),
      Same A N M (w ≫ fst T U) (w ≫ snd T U) ↔ ∃ z : Y ⟶ G, z ≫ i = w := fun Y w ↦
    (same_ev_param_iff hN.isLB hM.isLB _ _ w).symm.trans (hG Y w)
  obtain ⟨f, hfdef⟩ : ∃ f : G.left ⟶ T.left, f = (i ≫ fst T U).left := ⟨_, rfl⟩
  have hf : f ≫ T.hom = G.hom := by rw [hfdef]; exact Over.w (i ≫ fst T U)
  have hfz : ∀ {Y : Over (Sp R)} (z : Y ⟶ G), (z ≫ i ≫ fst T U).left = z.left ≫ f := fun z ↦ by
    rw [hfdef, Over.comp_left]
  haveI : IsClosedImmersion i.left := hi
  haveI : LocallyOfFiniteType (fst T U).left := inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom))
  haveI : LocallyOfFiniteType f := by
    rw [hfdef, Over.comp_left]; infer_instance
  haveI : Mono f := ⟨fun {Z} z₁ z₂ he ↦ by
    let a₁ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₁ rfl
    let a₂ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₂ (by
      simp only [Over.mk_hom]; rw [← hf, reassoc_of% he])
    have e₁ : a₁ ≫ i ≫ fst T U = a₂ ≫ i ≫ fst T U := by
      ext1; rw [hfz, hfz]; exact he
    have h₁ := (key _ (a₁ ≫ i)).2 ⟨a₁, rfl⟩
    have h₂ := (key _ (a₂ ≫ i)).2 ⟨a₂, rfl⟩
    simp only [Category.assoc] at h₁ h₂
    rw [← e₁] at h₂
    have e₂ : a₁ ≫ i ≫ snd T U = a₂ ≫ i ≫ snd T U :=
      hInj _ _ _ (same_of_same_of_same hN.isLB hM.isLB h₁ h₂)
    have e₃ : a₁ ≫ i = a₂ ≫ i := CartesianMonoidalCategory.hom_ext _ _ (by simpa using e₁) (by simpa using e₂)
    have e₄ := congrArg (fun q ↦ q.left) e₃
    simp only [Over.comp_left] at e₄
    exact (cancel_mono i.left).1 e₄⟩
  have hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B),
      I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ →
      ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ G.left) (b : Spec (CommRingCat.of B) ⟶ T.left),
        a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
        ∃ l : Spec (CommRingCat.of B) ⟶ G.left, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧
          l ≫ f = b := by
    intro B _ _ _ I hI hmI a b hab
    have ha : a ≫ G.hom = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom := by
      rw [← hf, reassoc_of% hab]
    let a' : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ G := Over.homMk a ha
    have hsame : Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ T) (a' ≫ i ≫ snd T U) := by
      have h₁ := (key _ (a' ≫ i)).2 ⟨a', rfl⟩
      have e : (a' ≫ i) ≫ fst T U = Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) := by
        ext1; rw [Category.assoc, hfz]; exact hab
      rw [e] at h₁
      simpa only [Category.assoc] using h₁
    obtain ⟨u, hu⟩ := hlift B I hI hmI b (a' ≫ i ≫ snd T U) hsame
    obtain ⟨z, hz⟩ := (key _ (lift (Over.homMk b rfl) u)).1 (by rwa [lift_fst, lift_snd])
    have hzf : z.left ≫ f = b := by
      rw [← hfz, ← Category.assoc, hz, lift_fst]; rfl
    refine ⟨z.left, ?_, hzf⟩
    rw [← cancel_mono f, Category.assoc, hzf, hab]
  haveI : IsOpenImmersion f := crit f hyp
  refine ⟨f.opensRange, fun Y y ↦ ⟨?_, fun hy ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨z, hz⟩ := (key Y (lift y u)).1 (by rwa [lift_fst, lift_snd])
    have e : z.left ≫ f = y.left := by rw [← hfz, ← Category.assoc, hz, lift_fst]
    rw [← e]
    exact ⟨z.left p, rfl⟩
  · have hr : Set.range y.left ⊆ Set.range f := by
      rintro _ ⟨p, rfl⟩
      simpa using hy p
    have hl : IsOpenImmersion.lift f y.left hr ≫ f = y.left := IsOpenImmersion.lift_fac f y.left hr
    let z : Y ⟶ G := Over.homMk (IsOpenImmersion.lift f y.left hr) (by rw [← hf, reassoc_of% hl, Over.w y])
    refine ⟨z ≫ i ≫ snd T U, ?_⟩
    have h₁ := (key Y (z ≫ i)).2 ⟨z, rfl⟩
    have e : (z ≫ i) ≫ fst T U = y := by
      ext1; rw [Category.assoc, hfz]; exact hl
    rwa [e, Category.assoc] at h₁

end GlobalTheory.DualCon
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_mono_finiteType_agreement_locus_injective_family : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U : Over S) [IsLocallyNoetherian T.left] [LocallyOfFiniteType U.hom] (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → Inj A M → ∃ (G : Over S) (π : G ⟶ T), Mono π.left ∧ LocallyOfFiniteType π.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), (∃ u : Y ⟶ U, Same A N M y u) ↔ ∃ z : Y.left ⟶ G.left, z ≫ π.left = y.left := by
  first | exact @GlobalTheory.DualGraph.exists_mono_same | exact GlobalTheory.DualGraph.exists_mono_same | (intros; apply GlobalTheory.DualGraph.exists_mono_same <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (F : Type) [Field F] [CharZero F] (b : Sp F ⟶ S), RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_isSemiAbelian | exact GlobalTheory.Nef.ratRigid_of_isSemiAbelian | (intros; apply GlobalTheory.Nef.ratRigid_of_isSemiAbelian <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityMap_extremalVector_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → HolAd θ M w (T v) := by
  first | exact @GlobalTheory.MultHol.holAd_of_isMultMap | exact GlobalTheory.MultHol.holAd_of_isMultMap | (intros; apply GlobalTheory.MultHol.holAd_of_isMultMap <;> assumption)
end
