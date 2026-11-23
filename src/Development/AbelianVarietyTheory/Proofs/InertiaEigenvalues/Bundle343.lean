module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle320
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle322
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerFunctorLeftExactTorsionCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s → characterTwistExists D.ntw D.nexp i s := by
  first | exact @GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | exact GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | (intros; apply GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.noInv_at_type_primes : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.NoLocalInvariants.noInv_of_adm2At | exact GlobalTheory.NoLocalInvariants.noInv_of_adm2At | (intros; apply GlobalTheory.NoLocalInvariants.noInv_of_adm2At <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
end

section

open CategoryTheory GlobalTheory.SelFun

theorem _root_.GlobalTheory.T.exists_torsion_module_extending_residue_maps : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P] [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P),
  ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
    ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  first | exact @GlobalTheory.SelFun.exists_torsion_extension | exact GlobalTheory.SelFun.exists_torsion_extension | (intros; apply GlobalTheory.SelFun.exists_torsion_extension <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ := by
  first | exact @GlobalTheory.NoGlobalInv.noInv | exact GlobalTheory.NoGlobalInv.noInv | (intros; apply GlobalTheory.NoGlobalInv.noInv <;> assumption)
end

section

open CategoryTheory GlobalTheory.SelFun

theorem _root_.GlobalTheory.T.leftExact_functor_representable_torsion_modules : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  first | exact @GlobalTheory.SelFun.Level.level | exact GlobalTheory.SelFun.Level.level | (intros; apply GlobalTheory.SelFun.Level.level <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hecke_preserves_good_part : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  first | exact @GlobalTheory.HkGoodStable.hkF_mem_V0 | exact GlobalTheory.HkGoodStable.hkF_mem_V0 | (intros; apply GlobalTheory.HkGoodStable.hkF_mem_V0 <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.localConditionAboveLSaturated_of_selmerSetup : LocalFiniteness → LocalTateDuality → LocalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → LocSat bkP i s κ := by
  first | exact @GlobalTheory.LocalSaturation.main | exact GlobalTheory.LocalSaturation.main | (intros; apply GlobalTheory.LocalSaturation.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.local_count_of_setup : LocalFiniteness → LocalTateDuality → LocalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → LocCount bkP i s κ := by
  first | exact @GlobalTheory.LocalConditionCount.locCount | exact GlobalTheory.LocalConditionCount.locCount | (intros; apply GlobalTheory.LocalConditionCount.locCount <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.selmer_functor_left_exact_torsion_coefficients : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelLeft bkP i s κ Q := by
  first | exact @GlobalTheory.SelLeftExact.selmer_left_exact | exact GlobalTheory.SelLeftExact.selmer_left_exact | (intros; apply GlobalTheory.SelLeftExact.selmer_left_exact <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem exists_algHom_groupRing {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (u : ι → A) (hu : ∀ q, u q ^ N = 1) :
    ∃ th : MonoidAlgebra R (Multiplicative (ι → ZMod N)) →ₐ[R] A,
      ∀ q, th (MonoidAlgebra.of R _ (Multiplicative.ofAdd (Pi.single q 1))) = u q := by
  let e : Multiplicative (ι → ZMod N) →* A :=
    { toFun := fun x => ∏ q, u q ^ (x.toAdd q).val
      map_one' := by simp
      map_mul' := fun x y => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add] }
  refine ⟨MonoidAlgebra.lift R A _ e, fun q => ?_⟩
  rw [MonoidAlgebra.lift_of]
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod N) : ι → ZMod N) p).val = u q
  rw [Finset.prod_eq_single q]
  · rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp, ZMod.val_zero, pow_zero]
  · simp

theorem X_pow_dvd_aeval_line {R K ι : Type} [CommRing R] [Field K] [Algebra R K] (b : ι → K) (n : ℕ)
    (F : MvPolynomial ι R) (h : ∀ m : ι →₀ ℕ, m.degree < n → algebraMap R K (F.coeff m) = 0) :
    (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) F := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.dvd_sum fun m _ => ?_
  by_cases hm : m.degree < n
  · rw [Polynomial.algebraMap_apply, h m hm, map_zero, zero_mul]
    exact dvd_zero _
  · refine Dvd.dvd.mul_left ?_ _
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (not_lt.1 hm)) _

theorem exists_unit_coeff_of_not_dvd_line (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    [Algebra (X.O0 i) K] (hK : IsRes i K) (b : ι → K) (n : ℕ) (hn : n ≤ X.l i ^ M) (F G : MvPolynomial ι (X.O0 i))
    (hFG : toLam X i M ι F = toLam X i M ι G)
    (hG : ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G) :
    ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  classical
  by_contra hcon
  apply hG
  have hF := X_pow_dvd_aeval_line b n F fun m hm => hK _ (fun hu => hcon ⟨m, hm, hu⟩)
  have hp := X.lPrime i
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu => by
    have := hu.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at this
    exact X.O_l i this
  have hlK : ((X.l i : ℕ) : K) = 0 := by
    have := hK _ hl0
    rwa [map_natCast] at this
  have : CharP K (X.l i) := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let I : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ n}
  let π : Polynomial K →ₐ[X.O0 i] (Polynomial K ⧸ I) := Ideal.Quotient.mkₐ (X.O0 i) I
  have hu : ∀ q, (π (Polynomial.C (b q) * Polynomial.X + 1)) ^ (X.l i ^ M) = 1 := fun q => by
    rw [← map_pow, add_pow_char_pow, one_pow, map_add (f := _), map_one, add_eq_right]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ?_)
    rw [mul_pow]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ hn) _
  obtain ⟨th, hth⟩ := exists_algHom_groupRing (R := X.O0 i) (X.l i ^ M) _ hu
  have hc : th.comp (toLam X i M ι) =
      π.comp (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    have := hth q
    simp only [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one]
    rw [sub_eq_iff_eq_add, ← map_one π, ← map_add (f := _), ← this]
  have h1 := DFunLike.congr_fun hc F
  have h2 := DFunLike.congr_fun hc G
  simp only [AlgHom.comp_apply] at h1 h2
  rw [hFG, h2] at h1
  have h3 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  simpa using dvd_add h3 hF

end GlobalTheory.ResSel
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.ResTrivConj

theorem map_eq_one_of_dual {R S n : Type} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n] (f : R →+* S)
    (A T' : GL n R) (T : Matrix n n R) (e : R) (t : ℕ) (hT : T.map f = 1) (he : f e = 1)
    (h : e • (T' : Matrix n n R)⁻¹.transpose =
      (A : Matrix n n R) * (e ^ t • T) * ((A⁻¹ : GL n R) : Matrix n n R)) :
    (T' : Matrix n n R).map f = 1 := by
  have hs : ∀ (c : R) (M : Matrix n n R), (c • M).map f = f c • M.map f := fun c M => by
    ext a b; simp
  have h1 := congrArg (fun M : Matrix n n R => M.map f) h
  simp only [Matrix.map_mul, hs, map_pow, he, hT, one_pow, one_smul, Matrix.mul_one] at h1
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f), Matrix.transpose_map,
    Matrix.transpose_eq_one, ← Matrix.coe_units_inv] at h1
  have h2 : ((T'⁻¹ : GL n R) : Matrix n n R).map f * (T' : Matrix n n R).map f = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]
  rwa [h1, Matrix.one_mul] at h2

theorem resTriv_conj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g g' : GE N, IsCj X g g' → ResTriv i s g → ResTriv i s g' := by
  intro D N X i s hsd g g' h hg
  have he : eps0 X i g' = eps0 X i g := by
    haveI := X.lPrime i
    have e : MulSemiringAction.toRingAut (GE N) N.Om g' =
        (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
      ext x; exact h x
    have : cycZ D.host.E N.Om (X.l i) g' = cycZ D.host.E N.Om (X.l i) g := by
      simp only [cycZ, MonoidHom.comp_apply]
      rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    simp only [eps0, MonoidHom.comp_apply, this]
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, by rw [he]; exact h2⟩
  obtain ⟨A, hA⟩ := hsd
  have hA' := hA g g' h
  rw [Tdual, he, ← Tgl_coe i s g'] at hA'
  rw [← Tgl_coe i s g']
  exact map_eq_one_of_dual _ A _ _ _ _ h1 h2 hA'

end GlobalTheory.ResTrivConj
end
