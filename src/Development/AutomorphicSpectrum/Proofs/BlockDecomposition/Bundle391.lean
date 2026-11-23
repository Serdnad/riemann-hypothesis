module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle384
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import GroundTheory.ProfiniteCohomology.Bundle001
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

@[expose] public section

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.Completion

theorem valuation_eq_exp_neg_one_of_mem_of_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F) (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.valuation F (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  apply GlobalTheory.LFun.EulerTie.valuation_of_mem_notMem_sq <;> assumption

theorem ord_algebraMap_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  intro F _ _ v ϖ h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion F]
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    GlobalTheory.adicCompletion_valuation_map_uniformiser F v (v.adicCompletion F) (RingEquiv.refl _)
      (fun a => by
        rw [GroundTheory.Global.mem_valuationInteger_iff]
        exact Iff.rfl) π hπ
  have hx : Valued.v (algebraMap F (v.adicCompletion F) (ϖ : F)) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ϖ : F)).trans
      (valuation_eq_exp_neg_one_of_mem_of_notMem F v ϖ h1 h2)
  have heq : valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (ϖ : F)) =
      valuation (v.adicCompletion F) (π : v.adicCompletion F) :=
    le_antisymm
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hx.trans hv.symm)))
      ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v _ _).2
        (le_of_eq (hv.trans hx.symm)))
  have hn := (normalizedValuation_eq_iff (K := v.adicCompletion F)).2 heq
  rw [← ord_uniformizer hπ]
  simp only [ord, hn]

end GlobalTheory.CompanionTheory.Completion
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

section Defs

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

def embBar (v : Pl (F := F)) : E →ₐ[F] FvBar F v := IsAlgClosed.lift

variable {F E} {J : Type} [Fintype J]

def supBar (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v) (u : J → E) : ℝ≥0 :=
  Finset.univ.sup fun f => absBar F v (τ (u f))

def locFin (σ : E →ₐ[F] E) (v : Pl (F := F)) (u : J → E) : ℝ≥0 :=
  supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u


open Classical in
def locInf (w : InfinitePlace F) (u : J → E) : ℝ≥0 :=
  (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ^ 2

def vecHt (σ : E →ₐ[F] E) (u : J → E) : ℝ≥0 := (∏ w : InfinitePlace F, locInf w u) * ∏ᶠ v, locFin σ v u

end Defs

section Minors

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def mnr (M : Matrix ι (Fin n) R) (f : Fin n → ι) : R := (M.submatrix f id).det

end Minors

end GlobalTheory.CompanionTheory.GodementH

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.exists_open_integral_subgroup : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | exact GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | (intros; apply GlobalTheory.CompanionTheory.Conc.LevelU.exists_level <;> assumption)
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Polarisation

noncomputable def cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

open Classical in
theorem cnt_apply {ι : Type} {m : ℕ} (f : Fin m → ι) (i : ι) :
    cnt f i = Fintype.card {j // f j = i} := by
  simp [cnt, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype]

theorem degree_cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : (cnt f).degree = m := by
  classical

  simp [cnt, map_sum]

theorem exists_perm_of_cnt_eq {ι : Type} {m : ℕ} {f g : Fin m → ι} (h : cnt f = cnt g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  have hc : ∀ i, Nonempty ({j // g j = i} ≃ {j // f j = i}) := fun i => by
    refine Fintype.card_eq.1 ?_
    rw [← cnt_apply, ← cnt_apply, h]
  let e : ∀ i, {j // g j = i} ≃ {j // f j = i} := fun i => (hc i).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

theorem prod_X_eq {ι : Type} {m : ℕ} (f : Fin m → ι) (a : Fin m → ℝ) :
    ∏ j, (C (a j) * X (f j) : MvPolynomial ι ℝ) = monomial (cnt f) (∏ j, a j) := by
  classical
  have key : ∀ s : Finset (Fin m), ∏ j ∈ s, (C (a j) * X (f j) : MvPolynomial ι ℝ)
      = monomial (∑ j ∈ s, Finsupp.single (f j) 1) (∏ j ∈ s, a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, X,
        C_mul_monomial, monomial_mul]
      simp
  exact key Finset.univ

theorem lin_pow {ι : Type} [Fintype ι] (n : ι → ℝ) (m : ℕ) :
    GlobalTheory.ArInt.lin n ^ m = ∑ f : Fin m → ι, monomial (cnt f) (∏ j, n (f j)) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset ι))
    (fun _ i => (C (n i) * X i : MvPolynomial ι ℝ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [GlobalTheory.ArInt.lin, h]
  exact Finset.sum_congr rfl fun f _ => prod_X_eq f (fun j => n (f j))


open Classical in
noncomputable def coef {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) : ℝ :=
  if h : ∃ f : Fin m → ι, cnt f = k then F h.choose else 0

theorem coef_cnt {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ)
    (hF : ∀ (f : Fin m → ι) (σ : Equiv.Perm (Fin m)), F (f ∘ σ) = F f) (f : Fin m → ι) :
    coef F (cnt f) = F f := by
  have h : ∃ g : Fin m → ι, cnt g = cnt f := ⟨f, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_cnt_eq h.choose_spec.symm
  rw [coef, dite_eq_left h, hσ, hF]

theorem coef_of_degree_ne {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) {k : ι →₀ ℕ}
    (hk : k.degree ≠ m) : coef F k = 0 := by
  refine dif_neg ?_
  rintro ⟨f, rfl⟩
  exact hk (degree_cnt f)

noncomputable def form {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials ι ℝ).constr ℝ (coef F)

theorem form_monomial {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) (a : ℝ) :
    form F (monomial k a) = a * coef F k := by
  have h1 : (monomial k a : MvPolynomial ι ℝ) = a • basisMonomials ι ℝ k := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h1, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

theorem exists_form (ι : Type) [Fintype ι] (D : ℕ) (F : (Fin (D + 1) → ι) → ℝ)
    (hF : ∀ (f : Fin (D + 1) → ι) (σ : Equiv.Perm (Fin (D + 1))), F (f ∘ σ) = F f) :
    ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
      (∀ n : ι → ℝ, Φ (GlobalTheory.ArInt.lin n ^ (D + 1)) = ∑ f : Fin (D + 1) → ι, (∏ j, n (f j)) * F f) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨form F, fun n => ?_, fun P d hd hP => ?_⟩

  · rw [lin_pow, map_sum]
    exact Finset.sum_congr rfl fun f _ => by rw [form_monomial, coef_cnt F hF]

  · rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hdeg : k.degree = d := by
      have := hP (mem_support_iff.1 hk)
      rw [Finsupp.degree_eq_weight_one]; exact this
    rw [form_monomial, coef_of_degree_ne F (by rw [hdeg]; exact hd), mul_zero]

end GlobalTheory.CompanionTheory.Polarisation
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DiagBd

theorem valued_eq_one_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w)
    (s : Fin n → (w.adicCompletion E)ˣ) (hg : g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹)
    (hc : IsCompact (closure (Subgroup.zpowers g : Set H))) (i : Fin n) :
    Valued.v (s i : w.adicCompletion E) = 1 := by
  set φ : H → w.adicCompletion E :=
    fun x => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) _) i i with hφdef
  have hφ : Continuous φ := by
    have h1 : Continuous fun x : H => (p⁻¹ * x.1 * p : GLw n w) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 : Continuous fun x : H => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
      Units.continuous_val.comp h1
    exact (continuous_apply i).comp ((continuous_apply i).comp h2)
  have hpow : ∀ m : ℤ, φ (g ^ m) = ((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro m
    have h1 : p⁻¹ * ((g ^ m : H) : GLw n w) * p = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) (s ^ m) := by
      rw [Subgroup.coe_zpow, hg, map_zpow]
      rw [show p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ =
        MulAut.conj p (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) from rfl, ← map_zpow]
      simp [MulAut.conj_apply, mul_assoc]
    simp only [hφdef, h1, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq, Pi.pow_apply]
  obtain ⟨R, hR⟩ := (hc.image hφ).isBounded.exists_norm_le
  have hb : ∀ m : ℤ, ‖((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ ≤ R := by
    intro m
    rw [← hpow m]
    exact hR _ ⟨g ^ m, subset_closure (Subgroup.zpow_mem_zpowers g m), rfl⟩
  have hne : (s i : w.adicCompletion E) ≠ 0 := (s i).ne_zero
  have hpos : 0 < ‖(s i : w.adicCompletion E)‖ := norm_pos_iff.mpr hne
  have hnorm : ‖(s i : w.adicCompletion E)‖ = 1 := by
    rcases lt_trichotomy ‖(s i : w.adicCompletion E)‖ 1 with h | h | h
    · exfalso
      have h' : 1 < ‖(s i : w.adicCompletion E)‖⁻¹ := (one_lt_inv₀ hpos).mpr h
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h'
      have := hb (-(k : ℤ))
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, _root_.zpow_neg, zpow_natCast, ← inv_pow] at this
      linarith
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h
      have := hb (k : ℤ)
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, zpow_natCast] at this
      linarith
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.1 hnorm.le) (not_lt.1 fun h => ?_)
  exact absurd (Valued.toNormedField.norm_lt_one_iff.2 h) (by rw [hnorm]; exact lt_irrefl _)

end GlobalTheory.CompanionTheory.DiagBd
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CptGen

theorem cptPart_eq_inf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (T C : Subgroup G), IsCompact (C : Set G) → (∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set G)) → t ∈ C) → cptPart T = T ⊓ C := by
  intro G _ _ _ _ T C hC h
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact ⟨hx.1, h x hx.1 hx.2⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed

end GlobalTheory.CompanionTheory.CptGen
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CentOk

theorem centraliser_hyps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  intro G _ _ _ _ θ hθ K I C δ hK hI hC hcpt x
  have hTc : IsClosed (twCent θ δ : Set G) := by
    have : (twCent θ δ : Set G) = {g | g * δ = δ * θ g} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hconj : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  constructor
  · have hKx : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.image hconj
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨hg.1, ?_⟩
    have hzp : (Subgroup.zpowers g : Set G) ⊆ (K.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
      (Subgroup.zpowers_le (G := G) (H := K.map (MulAut.conj x).toMonoidHom)).2 hg.2
    exact hKx.of_isClosed_subset isClosed_closure (closure_minimal hzp hKx.isClosed)
  · set A : Subgroup G := I.map (MulAut.conj x).toMonoidHom with hA
    have hAo : IsOpen (A : Set G) := by
      rw [hA, Subgroup.coe_map]
      exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hI
    have hHc : IsCompact (cptPart (twCent θ δ) : Set G) := by
      rw [hcpt, Subgroup.coe_inf]
      exact hC.inter_left hTc
    have hHT : cptPart (twCent θ δ) ≤ twCent θ δ := by
      rw [hcpt]; exact inf_le_left
    have e : (twCent θ δ ⊓ A) ⊓ cptPart (twCent θ δ) = A ⊓ cptPart (twCent θ δ) := by
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hHT h.2, h.1⟩, h.2⟩⟩
    rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
    haveI : CompactSpace (cptPart (twCent θ δ)) := isCompact_iff_compactSpace.mp hHc
    have ho : IsOpen ((A.subgroupOf (cptPart (twCent θ δ)) : Subgroup _) : Set (cptPart (twCent θ δ))) :=
      hAo.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.CentOk
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.UnrCM

theorem algebraMap_int_ringOfIntegers_surjective (F : Type) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 (x : F)
  have hx : IsIntegral ℤ (x : F) := x.isIntegral_coe
  have hint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff).1 (hq.symm ▸ hx)
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  simpa using hq

theorem finrank_maximalRealSubfield_of_subsingleton (E : Type) [Field E] [NumberField E] [IsCMField E]
    [Subsingleton (InfinitePlace E)] : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h1 : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h4 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h5
  omega

theorem nontrivial_infinitePlace_of_forall_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hn
  haveI : Subsingleton (InfinitePlace E) := not_nontrivial_iff_subsingleton.1 hn
  have hF := finrank_maximalRealSubfield_of_subsingleton E
  have hE : Module.finrank ℚ E ≠ 1 := by
    have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hF] at h5
    omega
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := E) (𝒪 := 𝓞 E) hE
  have hbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hw := hU ⟨P, hP.isPrime, hbot⟩
  apply hram
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P) := hw
  haveI : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ _)
      (algebraMap_int_ringOfIntegers_surjective _ hF)
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P)

theorem nontrivial_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) :=
  fun E _ _ _ hU => nontrivial_infinitePlace_of_forall_isUnramifiedAt E hU

end GlobalTheory.CompanionTheory.UnrCM
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace

theorem _root_.GlobalTheory.T.l2_convolution_locally_compact_mem : ∀ {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G), Continuous j → ∀ D : L → ℂ, Continuous D → HasCompactSupport D → ∀ φ ψ : G → ℂ, Continuous φ → ∀ h : MemL2Quotient Γ μ φ, (∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) → ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | exact GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | (intros; apply GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.fixed_vector_zero_of_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J, (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | exact GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.evaluation_maps_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
  eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | exact GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.local_constancy_twisted_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)), IsLocallyConstant (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) ∧ HasCompactSupport (fun d : Fin (t + 1) → k => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport | exact GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwFibre.twisted_fibre_isLocallyConstant_hasCompactSupport <;> assumption)
end
