module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.NumberTheory.NumberField.ProductFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X), (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  first | exact @GlobalTheory.PicGlue.rigOn_of_triv_open | exact GlobalTheory.PicGlue.rigOn_of_triv_open | (intros; apply GlobalTheory.PicGlue.rigOn_of_triv_open <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  first | exact @GlobalTheory.PicGlue.fnBij_snd | exact GlobalTheory.PicGlue.fnBij_snd | (intros; apply GlobalTheory.PicGlue.fnBij_snd <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.exists_variableChange_intV_of_j_mem : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ) (u : ℂˣ), W.j ∈ V → V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ → ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  first | exact @GlobalTheory.CMModel.exists_intV_variableChange | exact GlobalTheory.CMModel.exists_intV_variableChange | (intros; apply GlobalTheory.CMModel.exists_intV_variableChange <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.galoisStable_lattice_points_symmetric_mem : ∀ (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) → (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧ (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧ ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  first | exact @GlobalTheory.CMModel.stable_sym_mem | exact GlobalTheory.CMModel.stable_sym_mem | (intros; apply GlobalTheory.CMModel.stable_sym_mem <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.mem_of_duplication_eq_weierstrass : ∀ (V : ValuationSubring ℂ) (W : WeierstrassCurve ℂ) (x y δ : ℂ), IntV V W → W.toAffine.Equation x y → 2 * y + W.a₁ * x + W.a₃ ∈ V → δ ∈ V → x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ = (2 * y + W.a₁ * x + W.a₃) ^ 2 * (x + δ) → x ∈ V ∧ y ∈ V := by
  first | exact @GlobalTheory.CMModel.mem_of_duplication_eq | exact GlobalTheory.CMModel.mem_of_duplication_eq | (intros; apply GlobalTheory.CMModel.mem_of_duplication_eq <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' : ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ D : ℂ) (k : ℤ), a₄ ∈ F → a₆ ∈ F → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D → ModelAt V F (shortTwist (4 * (k : ℂ) + 1) a₄ a₆) ((4 * (k : ℂ) + 1) ^ 6 * D) := by
  first | exact @GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | exact GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one | (intros; apply GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.nonzeroSquaresModPrime_mul_perm_up_to_sign : ∀ (p c : ℕ), p.Prime → p % 4 = 3 → ¬ p ∣ c → ∃ (e : Sq p ≃ Sq p) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ ∀ k : Sq p, (p : ℤ) ∣ (((k.1 : ℕ) : ℤ) * c - ε * (((e k).1 : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.CMModel.sq_perm_mul | exact GlobalTheory.CMModel.sq_perm_mul | (intros; apply GlobalTheory.CMModel.sq_perm_mul <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  first | exact @GlobalTheory.sq_sum_equiv_Ico | exact GlobalTheory.sq_sum_equiv_Ico | (intros; apply GlobalTheory.sq_sum_equiv_Ico <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem _root_.GlobalTheory.T.deformed_lattice_sum_derivatives_eq_eisenstein_jets : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  first | exact @GlobalTheory.HilbFam.iterD_defSum_eq_jet | exact GlobalTheory.HilbFam.iterD_defSum_eq_jet | (intros; apply GlobalTheory.HilbFam.iterD_defSum_eq_jet <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  first | exact @GlobalTheory.HilbFam.jet_conj_expand | exact GlobalTheory.HilbFam.jet_conj_expand | (intros; apply GlobalTheory.HilbFam.jet_conj_expand <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic.HeightScaling

variable {F K : Type} [Field F] [Field K] [NumberField K] {N n : ℕ}

theorem finite_support_log {c : K} (hc : c ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (v c)).Finite := by
  refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport hc) fun v hv h1 => hv ?_
  simp only at h1
  simp [h1]

theorem sum_log_eq_zero {c : K} (hc : c ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v c)) + ∑ τ : K →+* ℂ, Real.log ‖τ c‖ = 0 := by
  have hmul : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  have h1 : ∑ᶠ w : FinitePlace K, Real.log (w c) = Real.log (∏ᶠ w : FinitePlace K, w c) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hc).ne')]
    intro w hw
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    simp [h1]
  have h2 : ∑ φ : K →+* ℂ, Real.log ‖φ c‖ = Real.log |Algebra.norm ℚ c| := by
    rw [← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 hc))]
    congr 1
    have := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ c)
    rw [norm_prod] at this
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => ‖φ c‖) (fun φ => ‖φ c‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← this]
    rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem finite_support_log_finSize {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    (φ : F →+* K) {y : Fin N → K} (hy : y ≠ 0) :
    (Function.support fun v : FinitePlace K => Real.log (finSize w φ v.1 y)).Finite := by
  have hfin : (⋃ k : {k : Fin n // ∑ j, φ (w j k) * y j ≠ 0},
      Function.mulSupport fun v : FinitePlace K => v (∑ j, φ (w j k.1) * y j)).Finite :=
    Set.finite_iUnion fun k => FinitePlace.hasFiniteMulSupport k.2
  refine hfin.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ k : Fin n, ∑ j, φ (w j k) * y j ≠ 0 → v.1 (∑ j, φ (w j k) * y j) = 1 := fun k hk => by
    by_contra h
    exact hn (Set.mem_iUnion.2 ⟨⟨k, hk⟩, h⟩)
  have hpos := finSize_pos hw φ v.1 hy
  have hle : finSize w φ v.1 y ≤ 1 := Real.iSup_le (fun k => by
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]; exact zero_le_one
    · exact (h1 k hk).le) zero_le_one
  have hge : 1 ≤ finSize w φ v.1 y := by
    by_contra h
    refine hpos.not_ge (Real.iSup_le (fun k => ?_) le_rfl)
    by_cases hk : ∑ j, φ (w j k) * y j = 0
    · rw [hk, map_zero]
    · exact absurd ((h1 k hk).ge.trans (le_finSize w φ v.1 y k)) h
  simp only [le_antisymm hle hge, Real.log_one]

theorem pointHeight_smul : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), Submodule.span F (Set.range w.col) = ⊤ → (∀ σ, (A σ).det ≠ 0) → ∀ (y : Fin N → K) (c : K), y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y := by
  intro F K _ _ _ _ _ N n w A hw hA y c hy hc
  rw [pointHeight_eq, pointHeight_eq]
  congr 1
  have e1 : ∀ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 (c • y)) =
      Real.log (v c) + Real.log (finSize w (algebraMap F K) v.1 y) := fun v => by
    rw [finSize_smul, Real.log_mul (v.1.ne_zero hc) (finSize_pos hw _ v.1 hy).ne']
    rfl
  have e2 : ∀ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ ((c • y) j)) =
      Real.log ‖τ c‖ + Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j)) := fun τ => by
    have h0 : (fun j => τ (y j)) ≠ 0 := fun h => hy (funext fun j => (map_eq_zero τ).1 (congrFun h j))
    have h1 : (fun j => τ ((c • y) j)) = τ c • fun j => τ (y j) := funext fun j => by simp
    rw [h1, archSize_smul, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero τ).2 hc)) (archSize_pos (hA _) h0).ne']
  rw [finsum_congr e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_add_distrib,
    finsum_add_distrib (finite_support_log hc) (finite_support_log_finSize hw _ hy)]
  linarith [sum_log_eq_zero hc]

end GlobalTheory.Adelic.HeightScaling
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.LieVB GlobalTheory.Conormal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

section Op

variable (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]

abbrev opModule : Module Oᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id O).fromOpposite fun x y => Commute.all x y)

theorem opModule_central : @IsCentralScalar O M _ (opModule O M).toSMul :=
  @IsCentralScalar.mk O M _ (opModule O M).toSMul fun _ _ => rfl

end Op

section Defs

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

abbrev TM : Over (Sp O) := Over.mk (spMap (algebraMap O (TrivSqZeroExt O M)))

def zeroSec : 𝟙_ (Over (Sp O)) ⟶ TM O M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom O O M).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isChart : IsChart (TM O M).hom (sec (zeroSec O M)) ⊤ ⊤ :=
  ⟨isAffineOpen_top (Sp O), isAffineOpen_top (Spec (CommRingCat.of (TrivSqZeroExt O M))), le_top, le_top⟩

abbrev topModule : Module Γ(Sp O, ⊤) M :=
  Module.compHom M (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

abbrev toTsze : Γ((TM O M).left, ⊤) →+* TrivSqZeroExt O M :=
  (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom.hom

abbrev toO : Γ(Sp O, ⊤) →+* O := (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

theorem toTsze_base (r : Γ(Sp O, ⊤)) :
    toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r) = algebraMap O _ (toO O r) := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (TrivSqZeroExt O M)))) r)

theorem toO_sec (b : Γ((TM O M).left, ⊤)) :
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) = (toTsze O M b).fst := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O M).toRingHom)) b)

end Defs

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Kappa

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

def sndFn : letI := (isChart O M).algebra; letI := topModule O M
    Γ((TM O M).left, ⊤) →ₗ[Γ(Sp O, ⊤)] M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  { toFun := fun b => (toTsze O M b).snd
    map_add' := fun a b => by simp
    map_smul' := fun r b => by
      change (toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r * b)).snd = toO O r • (toTsze O M b).snd
      rw [map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
      simp [TrivSqZeroExt.algebraMap_eq_inl] }

theorem sndFn_apply (b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M b = (toTsze O M b).snd := rfl

theorem sndFn_der (a b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M (a * b) = (isChart O M).aug (sec_hom _) a • sndFn O M b +
      (isChart O M).aug (sec_hom _) b • sndFn O M a := by
  letI := (isChart O M).algebra
  letI := topModule O M
  rw [sndFn_apply, sndFn_apply, sndFn_apply, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  change _ = (toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top a) • (toTsze O M b).snd : M) +
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) • (toTsze O M a).snd
  rw [toO_sec, toO_sec]

instance quasiCompact_zeroSec : QuasiCompact (sec (zeroSec O M)) := by
  have : QuasiSeparated (TM O M).hom := show QuasiSeparated (Spec.map _) from inferInstance
  infer_instance

def kappa : Γ(conormal (sec (zeroSec O M)), ⊤) →+ M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  ((AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M)).toAddMonoidHom).comp
    ((isChart O M).augCotEquiv (sec_hom _)).symm.toLinearMap.toAddMonoidHom

theorem kappa_d (b : Γ((TM O M).left, ⊤)) :
    kappa O M (d (sec_hom (zeroSec O M)) le_top b) = (toTsze O M b).snd := by
  letI := (isChart O M).algebra
  letI := topModule O M
  change (AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M))
    (((isChart O M).augCotEquiv (sec_hom _)).symm (d (sec_hom (zeroSec O M)) le_top b)) = _
  rw [← (isChart O M).augCotEquiv_d (sec_hom _) b, LinearEquiv.symm_apply_apply, AugCot.lift_d]
  rfl

end Kappa

section Phi

variable {O : Type} [CommRing O]


variable (A : Over (Sp O)) [GrpObj A] in
def Wmod : Type := Γ(omega A, ⊤)

instance (A : Over (Sp O)) [GrpObj A] : AddCommGroup (Wmod A) :=
  inferInstanceAs (AddCommGroup Γ(omega A, ⊤))

instance (A : Over (Sp O)) [GrpObj A] : Module O (Wmod A) :=
  Module.compHom Γ(omega A, ⊤) (cst O)

variable {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
  {A : Over (Sp O)} [GrpObj A]

def Phi (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) : Wmod A →+ M :=
  (kappa O M).comp (QCoh.appLinear (cotMap z h) ⊤).toAddMonoidHom

theorem Phi_apply (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (w : Wmod A) :
    Phi z h w = kappa O M ((cotMap z h).app ⊤ w) := rfl

end Phi

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Tower

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]


end Tower

end GlobalTheory.SqZeroPt
end
end
