module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorQuotientTorsionFreeComplete
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Module.PID
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfGenericIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompat
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedge
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section

open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TensorComplete

section Elementary

variable {A : Type} [CommRing A] (π : A)

theorem smodEq_span_iff {M : Type} [AddCommGroup M] [Module A M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule A M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem isAdicComplete_span_iff {M : Type} [AddCommGroup M] [Module A M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  apply GlobalTheory.XiQuotient.isAdicComplete_iff <;> assumption

variable {π}

theorem isAdicComplete_of_linearEquiv {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · have : e.symm x = 0 := h1 _ fun n => by
      obtain ⟨z, hz⟩ := hx n
      exact ⟨e.symm z, by rw [← map_smul, hz]⟩
    simpa using this
  · obtain ⟨L, hL⟩ := h2 (fun n => e.symm (u n)) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨e.symm z, by rw [← map_smul, hz, map_sub]⟩
    refine ⟨e L, fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    exact ⟨e z, by rw [← map_smul, hz, map_sub, LinearEquiv.apply_symm_apply]⟩

theorem isAdicComplete_prod {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : IsAdicComplete (Ideal.span {π}) M)
    (h' : IsAdicComplete (Ideal.span {π}) M') : IsAdicComplete (Ideal.span {π}) (M × M') := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  obtain ⟨h1', h2'⟩ := (isAdicComplete_span_iff π).1 h'
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · refine Prod.ext (h1 _ fun n => ?_) (h1' _ fun n => ?_)
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.1, by rw [← hz]; rfl⟩
    · obtain ⟨z, hz⟩ := hx n
      exact ⟨z.2, by rw [← hz]; rfl⟩
  · obtain ⟨L, hL⟩ := h2 (fun n => (u n).1) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.1, by simpa using congrArg Prod.fst hz⟩
    obtain ⟨L', hL'⟩ := h2' (fun n => (u n).2) fun n => by
      obtain ⟨z, hz⟩ := hu n
      exact ⟨z.2, by simpa using congrArg Prod.snd hz⟩
    refine ⟨(L, L'), fun n => ?_⟩
    obtain ⟨z, hz⟩ := hL n
    obtain ⟨z', hz'⟩ := hL' n
    exact ⟨(z, z'), Prod.ext hz hz'⟩

theorem isAdicComplete_fin_pi {M : Type} [AddCommGroup M] [Module A M]
    (h : IsAdicComplete (Ideal.span {π}) M) (n : ℕ) :
    IsAdicComplete (Ideal.span {π}) (Fin n → M) := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_span_iff π).1 h
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · funext i
    refine h1 _ fun k => ?_
    obtain ⟨z, hz⟩ := hx k
    exact ⟨z i, by rw [← hz]; rfl⟩
  · choose z hz using hu
    have key : ∀ i : Fin n, ∃ L : M, ∀ k : ℕ, ∃ w : M, π ^ k • w = u k i - L := fun i =>
      h2 (fun k => u k i) fun k => ⟨z k i, by simpa using congrFun (hz k) i⟩
    choose L hL using key
    refine ⟨L, fun k => ?_⟩
    choose w hw using fun i => hL i k
    exact ⟨w, funext hw⟩

theorem isAdicComplete_of_pow_smul_eq_zero {M : Type} [AddCommGroup M] [Module A M] (E : ℕ)
    (h : ∀ x : M, π ^ E • x = 0) : IsAdicComplete (Ideal.span {π}) M := by
  refine (isAdicComplete_span_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · obtain ⟨z, rfl⟩ := hx E
    exact h z
  · have tel : ∀ n k : ℕ, ∃ z : M, π ^ n • z = u n - u (n + k) := by
      intro n k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨w, hw⟩ := hu (n + k)
        refine ⟨z + π ^ k • w, ?_⟩
        rw [smul_add, smul_smul, ← pow_add, hz, hw, ← add_assoc]
        abel
    refine ⟨u E, fun n => ?_⟩
    obtain ⟨z, hz⟩ := tel n E
    obtain ⟨w, hw⟩ := tel E n
    rw [h w, add_comm E n] at hw
    refine ⟨z, ?_⟩
    rw [hz, ← sub_eq_zero.1 hw.symm]

end Elementary

section Tensor

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

theorem irreducible_dvd_of_not_isUnit {q r : R} (hq : Irreducible q) (hr : ¬IsUnit r) : q ∣ r := by
  have hmax : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq
  have heq : Ideal.span {q} = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← Ideal.mem_span_singleton, heq]
  exact (IsLocalRing.mem_maximalIdeal r).2 hr

theorem exists_pow_smul_directSum_eq_zero {ι : Type} [Fintype ι] (q : ι → R)
    (hq : ∀ i, Irreducible (q i)) (e : ι → ℕ) {r : R} (hr : ¬IsUnit r) :
    ∃ E : ℕ, ∀ x : DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i}), r ^ E • x = 0 := by
  classical
  refine ⟨∑ i, e i, fun x => ?_⟩
  refine DFinsupp.ext fun i => ?_
  have hmem : r ^ (∑ i, e i) ∈ Submodule.span R {q i ^ e i} := by
    rw [Submodule.mem_span_singleton]
    have h1 : q i ^ e i ∣ r ^ (∑ i, e i) :=
      (pow_dvd_pow_of_dvd (irreducible_dvd_of_not_isUnit (hq i) hr) (e i)).trans
        (pow_dvd_pow r (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
  change r ^ (∑ i, e i) • x i = 0
  rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simpa [smul_eq_mul, mul_comm] using Submodule.smul_mem _ y hmem

theorem pow_natCast_smul_tensor_eq_zero {O T : Type} [CommRing O] [Algebra R O] [AddCommGroup T]
    [Module R T] (p E : ℕ) (h : ∀ x : T, (p : R) ^ E • x = 0) (t : O ⊗[R] T) :
    (p : O) ^ E • t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o x =>
    have h1 : (p : O) ^ E * o = (p : R) ^ E • o := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [TensorProduct.smul_tmul', smul_eq_mul, h1, TensorProduct.smul_tmul, h x,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

end Tensor

theorem isAdicComplete_tensor : ∀ (p : ℕ) [Fact p.Prime] (R O : Type) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsLocalRing R] [CommRing O] [Algebra R O]
    [IsAdicComplete (Ideal.span {(p : O)}) O],
    (p : R) ≠ 0 → ¬IsUnit (p : R) →
    ∀ (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] N) := by
  intro p _ R O _ _ _ _ _ _ _ hp1 hp2 N _ _ _
  obtain ⟨n, ι, _, q, hq, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := N)
  obtain ⟨E, hE⟩ := exists_pow_smul_directSum_eq_zero q hq e hp2
  have hfree : IsAdicComplete (Ideal.span {(p : O)}) (O ⊗[R] (Fin n →₀ R)) :=
    isAdicComplete_of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite O O (Fin n)).symm.trans
        (TensorProduct.finsuppScalarRight R O O (Fin n)).symm)
      (isAdicComplete_fin_pi inferInstance n)
  have htors : IsAdicComplete (Ideal.span {(p : O)})
      (O ⊗[R] DirectSum ι (fun i => R ⧸ Submodule.span R {q i ^ e i})) :=
    isAdicComplete_of_pow_smul_eq_zero E (pow_natCast_smul_tensor_eq_zero p E hE)
  exact isAdicComplete_of_linearEquiv
    ((TensorProduct.prodRight R O O _ _).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl O O) f).symm)
    (isAdicComplete_prod hfree htors)

end GlobalTheory.CompanionTheory.TensorComplete
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def scalH (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) : HermR R σ n :=
  ⟨(algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h : sigR R σ (algebraMap R (R ⊗[F] E) l) = algebraMap R (R ⊗[F] E) l := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h, S.2 a b]⟩

theorem scalH_coe (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) :
    (scalH R σ l S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl

theorem scalH_hermScal (σ : E →ₐ[F] E) (l s : R) :
    scalH R σ l (hermScal R σ s) = hermScal R σ (l * s) := by
  apply Subtype.ext
  funext a b
  change (algebraMap R (R ⊗[F] E) l) * (s ⊗ₜ[F] (1 : E)) = (l * s) ⊗ₜ[F] (1 : E)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

end Alg

theorem euler_move_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → ∀ κ : ℝ≥0, IsEulerProd b I κ minf m → IsEulerProd b (I.map e) κ minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf κ hE
  have tr : ∀ (J : Measure (Fin n → Fin M → AF F ⊗[F] E)) (a : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (w : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsEulerProd b J κ a w ↔ IsEulerProd b J 1 (κ • a) w := fun J a w => by
    have e1 : ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, ∫⁻ X, φ X ∂(κ • a) = (κ : ℝ≥0∞) * ∫⁻ X, φ X ∂a := fun φ => by
      rw [ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
    simp only [IsEulerProd, e1, ENNReal.coe_one, one_mul, mul_assoc]
  rw [tr] at hE ⊢
  refine PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move F E σ hcm d b n M I _ _ m m' e ei ev me mei mev hpr hG ci c hc ?_ h2 hf hE
  rw [Measure.map_smul κ mei.aemeasurable, h1, smul_comm]

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.perfect_of_generic_iso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y}, M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M) := by
  first | exact @GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | exact GlobalTheory.CompanionTheory.PerfIso.perf_of_iso | (intros; apply GlobalTheory.CompanionTheory.PerfIso.perf_of_iso <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.forms_restrict_open_bijective : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ),
    Function.Bijective fun x : OmU q V a => formRes (V.ι ≫ q) (show (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V by simp) a
      (formPull (f := V.ι) rfl V a x) := by
  first | exact @GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | exact GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective | (intros; apply GlobalTheory.CompanionTheory.FormOpen.formRes_formPull_open_bijective <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.cone_forms_map_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ), Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.card_hermitian_representations_residue : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det → (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | exact GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem gr_pull_g {X Y Z : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : F (r z) ∈ M.U i) (hj : F (r z) ∈ M.U j)
    (hm : r z ∈ (M.pull F).U (fun _ => i) ⊓ (M.pull F).U (fun _ => j)) :
    gr r z _ hm ((M.pull F).g (fun _ => i) (fun _ => j)).val =
      gr (r ≫ F) z (M.U i ⊓ M.U j) ⟨hi, hj⟩ (M.g i j).val := by
  refine (congrArg (fun u => gr r z _ hm (Units.val u))
    ((Fintype.prod_unique (fun _ : PUnit => _ ^ (1 : ℤ))).trans (zpow_one _))).trans ?_
  exact gr_res r z _ hm _

theorem app_eq_zero_of_mem_ext {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    (U : X.Opens) {a : Γ(X, U)} (ha : a ∈ ext s J U) :
    ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom a = 0 := by
  have hle : ext s J U ≤
      RingHom.ker ((pullback.fst s (spMap (Ideal.Quotient.mk J))).app U).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker,
      app_cst (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))).w U r,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  exact hle ha

theorem triv_of_compatible_mod (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R)
    (M : LB X) (hM : M.IsLB) (A : Type) (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (hV : ⨆ a, V a = ⊤) (y z : ∀ a, Γ(X, V a))
    (hyz : ∀ a, y a * z a - 1 ∈ ext s J (V a))
    (hc : ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
      ext s J (V a ⊓ V b)) :
    GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) := by
  set π := pullback.fst s (spMap (Ideal.Quotient.mk J)) with hπ
  have cov : ⨆ a, π ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV]; rfl
  refine gen_of_refine (pull_isLB hM π) (fun a => π ⁻¹ᵁ V a) cov (fun a _ => j a)
    (fun a => pull_le M π (j a) (hj a)) (fun a => (π.app (V a)).hom (y a))
    (fun a => IsUnit.of_mul_eq_one ((π.app (V a)).hom (z a)) ?_) fun a b x ha hb => ?_
  · have h := app_eq_zero_of_mem_ext s J (V a) (hyz a)
    rw [map_sub, map_mul, map_one, sub_eq_zero] at h
    exact h
  · have hab : (𝟙 _ : pullback s (spMap (Ideal.Quotient.mk J)) ⟶ _) x ∈ π ⁻¹ᵁ (V a ⊓ V b) :=
      ⟨ha, hb⟩
    have h := congrArg (gr (𝟙 _) x (π ⁻¹ᵁ (V a ⊓ V b)) hab)
      (app_eq_zero_of_mem_ext s J (V a ⊓ V b) (hc a b))
    rw [map_zero, gr_app, map_sub, map_mul, tr, gr_res, gr_res, gr_res, sub_eq_zero] at h
    refine (gr_app _ _ _ _ _ _).trans (h.trans ?_)
    rw [gr_app]
    exact congrArg (· * _) (gr_pull_g M π (𝟙 _) x (hj a ha) (hj b hb) _).symm

end GlobalTheory.CompanionTheory.FewEq
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_pullback_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  first | exact @GlobalTheory.CompanionTheory.OmNatT.pull_nat | exact GlobalTheory.CompanionTheory.OmNatT.pull_nat | (intros; apply GlobalTheory.CompanionTheory.OmNatT.pull_nat <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

theorem _root_.GlobalTheory.T.hodge_form_cup_wedge : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  first | exact @GlobalTheory.CompanionTheory.OmCup.main | exact GlobalTheory.CompanionTheory.OmCup.main | (intros; apply GlobalTheory.CompanionTheory.OmCup.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem resLoc : CrystallineSemistableComparison.E.ResLoc := by
  intro R _ F s U x hx
  exact (GlobalTheory.EtC.resSec R F U).2.2.1 (s : ℤ) ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ) (by omega) (by omega) x (by omega) hx

end GlobalTheory.CompanionTheory.EdgeMap
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRes

theorem resZero : CrystallineSemistableComparison.E.ResZero := by
  intro R _ F U
  obtain ⟨h0, h1, -, h3⟩ := GlobalTheory.EtC.resSec R F U
  exact ⟨h1, h0, h3⟩

end GlobalTheory.CompanionTheory.EtRes
end
