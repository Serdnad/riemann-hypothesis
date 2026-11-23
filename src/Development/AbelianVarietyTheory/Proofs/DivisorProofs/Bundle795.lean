module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle788
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle091
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActRel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def prodPow {r : ℕ} (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ) : A ⟶ A := ∏ k, f k ^ c k

theorem prodPow_add {r : ℕ} (f : Fin r → (A ⟶ A)) (c d : Fin r → ℤ) :
    prodPow f (c + d) = prodPow f c * prodPow f d := by
  simp [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_zero {r : ℕ} (f : Fin r → (A ⟶ A)) : prodPow f 0 = 1 := by
  simp [prodPow]

theorem prodPow_zsmul {r : ℕ} (f : Fin r → (A ⟶ A)) (n : ℤ) (c : Fin r → ℤ) :
    prodPow f (n • c) = prodPow f c ^ n := by
  simp [prodPow, zpow_mul', Finset.prod_zpow]

theorem prodPow_single {r : ℕ} (f : Fin r → (A ⟶ A)) (k : Fin r) : prodPow f (Pi.single k 1) = f k := by
  unfold prodPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def prodPowHom {r : ℕ} (f : Fin r → (A ⟶ A)) : Multiplicative (Fin r → ℤ) →* (A ⟶ A) :=
  MonoidHom.mk' (fun c => prodPow f c.toAdd) (fun c d => prodPow_add f c.toAdd d.toAdd)

theorem prodPow_sum {r : ℕ} (f : Fin r → (A ⟶ A)) {J : Type} (s : Finset J) (g : J → Fin r → ℤ) :
    prodPow f (∑ i ∈ s, g i) = ∏ i ∈ s, prodPow f (g i) := by
  have := map_prod (prodPowHom f) (fun i => Multiplicative.ofAdd (g i)) s
  rw [← ofAdd_sum] at this
  exact this

def precompHom (h : A ⟶ A) : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => h ≫ x) (fun x y => MonObj.comp_mul h x y)

def postcompHom (h : A ⟶ A) [IsMonHom h] : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => x ≫ h) (fun x y => MonObj.mul_comp x y h)

end GlobalTheory.ActRel

namespace GlobalTheory.ActRel

theorem prodPow_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (cm : Fin r → Fin r → Fin r → ℤ) (hm : ∀ i j, f i ≫ f j = prodPow f (cm i j))
    (c d : Fin r → ℤ) :
    prodPow f c ≫ prodPow f d = prodPow f (∑ k, ∑ l, (c k * d l) • cm k l) := by
  haveI : IsMonHom (prodPow f d) := isMonHom_prodPow f hf d
  have h1 : prodPow f c ≫ prodPow f d = ∏ k, (f k ≫ prodPow f d) ^ c k := by
    have := map_prod (postcompHom (prodPow f d)) (fun k => f k ^ c k) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun k _ => ?_)
    show (f k ^ c k) ≫ prodPow f d = _
    exact GrpObj.zpow_comp (f k) (c k) (prodPow f d)
  have h2 : ∀ k, f k ≫ prodPow f d = ∏ l, prodPow f (cm k l) ^ d l := by
    intro k
    have := map_prod (precompHom (f k)) (fun l => f l ^ d l) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun l _ => ?_)
    show f k ≫ f l ^ d l = _
    rw [GrpObj.comp_zpow, hm]
  rw [h1, prodPow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h2, prodPow_sum, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prodPow_zsmul, ← zpow_mul, mul_comm]

theorem ringAct_iff_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O),
    Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ)
      (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
      (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔
        ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧
          ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  intro O _ r e he
  let φ : (Fin r → ℤ) →ₗ[ℤ] O :=
    { toFun := fun c => ∑ k, c k • e k
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun n c => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ k, c k • e k := fun _ => rfl
  have hsurj : ∀ a, ∃ c, φ c = a := fun a => by
    have : a ∈ Submodule.span ℤ (Set.range e) := he ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
    exact ⟨c, hc⟩
  obtain ⟨m, N, hN⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  choose coef hcoef using hsurj
  refine ⟨m, N, coef 1, fun i j => coef (e i * e j), ?_⟩
  intro S A _ _ f hf
  have hker : (∀ j, prodPow f (N j) = 1) → ∀ c ∈ LinearMap.ker φ, prodPow f c = 1 := by
    intro hNj c hc
    rw [← hN] at hc
    induction hc using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hNj j
    | zero => exact prodPow_zero f
    | add x y _ _ hx hy => rw [prodPow_add, hx, hy, _root_.mul_one]
    | smul n x _ hx => rw [prodPow_zsmul, hx, one_zpow]
  have hwd : (∀ j, prodPow f (N j) = 1) → ∀ c d, φ c = φ d → prodPow f c = prodPow f d := by
    intro hNj c d h
    have hcd : c - d ∈ LinearMap.ker φ := by simp [LinearMap.mem_ker, map_sub, h]
    calc prodPow f c = prodPow f (d + (c - d)) := by rw [add_sub_cancel]
      _ = prodPow f d := by rw [prodPow_add, hker hNj _ hcd, _root_.mul_one]
  have hmul : ∀ c d : Fin r → ℤ, φ c * φ d = ∑ k, ∑ l, (c k * d l) • (e k * e l) := by
    intro c d
    rw [hφ, hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_smul]
  constructor
  · rintro ⟨act, hact, hek⟩
    have h0 : act 0 = 1 := by
      have := hact.2.2.2 0 0
      rw [add_zero] at this
      exact mul_eq_left.mp this.symm
    let H : Multiplicative O →* (A ⟶ A) :=
      MonoidHom.mk' (fun a => act a.toAdd) (fun a b => hact.2.2.2 a.toAdd b.toAdd)
    have hact' : ∀ c, act (φ c) = prodPow f c := by
      intro c
      have : act (φ c) = H (Multiplicative.ofAdd (∑ k, c k • e k)) := rfl
      rw [this, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      show act (e k) ^ c k = _
      rw [hek]
    refine ⟨fun j => ?_, ?_, fun i j => ?_⟩
    · show prodPow f (N j) = 1
      have hNj : N j ∈ LinearMap.ker φ := hN ▸ Submodule.subset_span ⟨j, rfl⟩
      rw [← hact', LinearMap.mem_ker.mp hNj, h0]
    · show prodPow f (coef 1) = 𝟙 A
      rw [← hact', hcoef, hact.2.1]
    · show f i ≫ f j = prodPow f (coef (e i * e j))
      rw [← hact', hcoef, hact.2.2.1, hek, hek]
  · rintro ⟨hNj, h1, hm⟩
    refine ⟨fun a => prodPow f (coef a), ⟨fun a => isMonHom_prodPow f hf _, h1, fun a b => ?_, fun a b => ?_⟩,
      fun k => ?_⟩
    · rw [prodPow_comp f hf _ hm]
      apply hwd hNj

      rw [hcoef, map_sum]

      simp only [map_sum, map_zsmul, hcoef]
      rw [← hmul, hcoef, hcoef]
    · rw [← prodPow_add]
      apply hwd hNj
      rw [map_add (f := _), hcoef, hcoef, hcoef]
    · show prodPow f (coef (e k)) = f k
      rw [hwd hNj (coef (e k)) (Pi.single k 1) (by rw [hcoef, hφ]; simp [Pi.single_apply]),
        prodPow_single]

end GlobalTheory.ActRel
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.Wedge

def alt2 {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) : M [⋀^Fin 2]→ₗ[R] N where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all

theorem alt2_apply {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] M →ₗ[R] N) (hf : ∀ x, f x x = 0) (v : Fin 2 → M) : alt2 f hf v = f (v 0) (v 1) := rfl

theorem bijective_of_fibres {R B C : Type} [CommRing R] [AddCommGroup B] [Module R B] [AddCommGroup C]
    [Module R C] [Module.Finite R B] [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ q : PrimeSpectrum R, Function.Bijective (l.baseChange q.asIdeal.ResidueField)) :
    Function.Bijective l := by
  have hlt : ∀ q : PrimeSpectrum R, Function.Bijective (l.lTensor q.asIdeal.ResidueField) := by
    intro q
    have e : ⇑(l.lTensor q.asIdeal.ResidueField) = ⇑(l.baseChange q.asIdeal.ResidueField) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    rw [e]; exact h q
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective l
      (fun m hm => (hlt ⟨m, hm.isPrime⟩).1)
    exact Function.LeftInverse.injective (g := r) fun x => LinearMap.congr_fun hr x
  · have hQ : Subsingleton (C ⧸ LinearMap.range l) := by
      apply GlobalTheory.subsingleton_of_residueField_fibres R
      intro q
      have h2 := (hlt q).2
      have h3 : Function.Surjective ((LinearMap.range l).mkQ.lTensor q.asIdeal.ResidueField) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun a b => ?_⟩
      have key : ∀ a : q.asIdeal.ResidueField ⊗[R] (C ⧸ LinearMap.range l), a = 0 := by
        intro a
        obtain ⟨x, rfl⟩ := h3 a
        obtain ⟨y, rfl⟩ := h2 x
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp]
        simp
      rw [key a, key b]
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hQ

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

def wedgeMap (hsq : ∀ x : HO1 s, cup _ x x = 0) : ⋀[R]^2 (HO1 s) →ₗ[R] HO2 s :=
  exteriorPower.alternatingMapLinearEquiv (alt2 (cup _) hsq)

theorem wedgeMap_ιMulti (hsq : ∀ x : HO1 s, cup _ x x = 0) (v : Fin 2 → HO1 s) :
    wedgeMap s hsq (exteriorPower.ιMulti R 2 v) = cup _ (v 0) (v 1) := by
  simp only [wedgeMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, alt2_apply]

theorem baseChange_wedgeMap_bijective (hsq : ∀ x : HO1 s, cup _ x x = 0) (k : Type) [CommRing k]
    [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X)
    (hpb : φ ≫ s = s' ≫ spMap (algebraMap R k))
    (e1 : k ⊗[R] HO1 s ≃ₗ[k] HO1 s') (he1 : ∀ c, e1 (1 ⊗ₜ c) = pullHO1 hpb c)
    (e2 : k ⊗[R] HO2 s ≃ₗ[k] HO2 s') (he2 : ∀ c, e2 (1 ⊗ₜ c) = pullHO2 hpb c)
    (w : ⋀[k]^2 (CatCoh.H1 (OAff s')) ≃ₗ[k] CatCoh.H2 (OAff s'))
    (hw : ∀ a b, w (exteriorPower.ιMulti k 2 ![a, b]) = cup _ a b) :
    Function.Bijective ((wedgeMap s hsq).baseChange k) := by
  have hcup := ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 R k X X' s s' (algebraMap R k) φ hpb).1
  let β := (GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange R (HO1 s) k) 2).equiv
  let T : k ⊗[R] ⋀[R]^2 (HO1 s) →ₗ[k] k ⊗[R] HO2 s :=
    e2.symm.toLinearMap ∘ₗ w.toLinearMap ∘ₗ exteriorPower.map 2 e1.toLinearMap ∘ₗ β.toLinearMap
  have hT : T = (wedgeMap s hsq).baseChange k := by
    refine TensorProduct.AlgebraTensorModule.ext fun c x => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hl : (T.restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 =
        (((wedgeMap s hsq).baseChange k).restrictScalars R) ∘ₗ TensorProduct.mk R k _ 1 := by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        wedgeMap_ιMulti, T, LinearEquiv.coe_coe, β, IsBaseChange.equiv_tmul, one_smul,
        GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.map_apply_ιMulti]
      have hv : (⇑e1 ∘ fun i => (1 : k) ⊗ₜ[R] v i) = ![pullHO1 hpb (v 0), pullHO1 hpb (v 1)] := by
        funext i; fin_cases i <;> simp [he1]
      rw [hv, hw, LinearEquiv.symm_apply_eq, he2, hcup]
    exact LinearMap.congr_fun hl x
  rw [← hT]
  have hm : Function.Bijective (exteriorPower.map 2 e1.toLinearMap) := by
    refine Function.bijective_iff_has_inverse.2 ⟨exteriorPower.map 2 e1.symm.toLinearMap, ?_, ?_⟩
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
    · intro x
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp [exteriorPower.map_id]
  exact e2.symm.bijective.comp (w.bijective.comp (hm.comp β.bijective))

end GlobalTheory.AbCoh.Wedge

namespace GlobalTheory.AbCoh.Wedge

theorem wedgeO_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by
  intro R _ X s hF1 hP1 hF2 hP2 hB1 hB2 hsq hfib
  have hbij : Function.Bijective (wedgeMap s hsq) := by
    refine bijective_of_fibres _ fun q => ?_
    obtain ⟨X', s', φ, hpb⟩ : ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp q.asIdeal.ResidueField) (φ : X' ⟶ X),
        IsPullback φ s' s (spMap (algebraMap R q.asIdeal.ResidueField)) :=
      ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
    obtain ⟨e1, he1⟩ := hB1 _ _ _ _ hpb
    obtain ⟨e2, he2⟩ := hB2 _ _ _ _ hpb
    obtain ⟨w, hw⟩ := hfib _ _ _ _ hpb
    exact baseChange_wedgeMap_bijective s hsq _ X' s' φ hpb.w e1 he1 e2 he2 w hw
  exact ⟨LinearEquiv.ofBijective _ hbij, fun a b => by
    rw [LinearEquiv.ofBijective_apply, wedgeMap_ιMulti]; rfl⟩

end GlobalTheory.AbCoh.Wedge
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section PairNat

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' Y Y' : Scheme.{0}}
  {φ : X' ⟶ X} {χ : Y' ⟶ Y} {ψ : Y ⟶ X} {ψ' : Y' ⟶ X'}

theorem pre_le_pre (e : ψ' ≫ φ = χ ≫ ψ) {V : Y.Opens} {U : X.Opens} (hp : V ≤ ψ ⁻¹ᵁ U) :
    χ ⁻¹ᵁ V ≤ ψ' ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
  exact fun x hx ↦ hp hx

variable [IsAffineHom φ] [IsAffineHom χ]

def prePairMap (e : ψ' ≫ φ = χ ≫ ψ) (p : Pair ψ) : Pair ψ' :=
  ⟨(preU χ p.1.1, preU φ p.1.2), pre_le_pre e p.2⟩

theorem prePairMap_mono (e : ψ' ≫ φ = χ ≫ ψ) : Monotone (prePairMap e) := fun _ _ h ↦
  show _ ∧ _ from ⟨preU_mono χ (Pair.le_fst h), preU_mono φ (Pair.le_snd h)⟩

def preFun (e : ψ' ≫ φ = χ ≫ ψ) : (Pair ψ)ᵒᵖ ⥤ (Pair ψ')ᵒᵖ := (prePairMap_mono e).functor.op

variable {s' : X' ⟶ Sp R'} {q' : Y' ⟶ Sp R'}


variable (s' q') in
def preCoefPair (e : ψ' ≫ φ = χ ≫ ψ) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) :
    CoefMap (RingHom.id R') (OPre φ s') (pairFst ψ ⋙ OPre χ q') where
  G := pairSnd ψ
  α p := secPull s' q' (prePairMap e p.unop)
  naturality a b := (pairPull w').naturality ((preFun e).map a) b
  smul p := semiHom_secPull w' (prePairMap e p.unop)

end PairNat

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by
  intro R R' _ _ σ X X' Y Y' s s' q q' φ χ _ h ψ ψ' w w' e hφ
  haveI := hφ
  have H := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h
  let m := preCoefPair s' q' e w'
  let Φ := preFun (φ := φ) (χ := χ) e
  have hα : ∀ (p : (Pair ψ)ᵒᵖ) (b : (OAff s).obj ((pairSnd ψ).obj p)),
      m.α p (preα φ s s' ((pairSnd ψ).obj p) b) =
        preα χ q q' ((pairFst ψ).obj p) ((pairPull w).α p b) := by
    intro p b
    have k1 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE ψ' φ _ _ _
      (prePair φ p.unop.1.2).2 (prePairMap e p.unop).2)
    have k2 := congrArg (fun t ↦ t.hom b) (Scheme.Hom.appLE_comp_appLE χ ψ _ _ _
      p.unop.2 (prePair χ p.unop.1.1).2)
    have k3 : ∀ (g₁ g₂ : Y' ⟶ X) (_ : g₁ = g₂) (h1 : (preU χ p.unop.1.1).1 ≤ g₁ ⁻¹ᵁ p.unop.1.2.1)
        (h2 : (preU χ p.unop.1.1).1 ≤ g₂ ⁻¹ᵁ p.unop.1.2.1) (x : Γ(X, p.unop.1.2.1)),
        (g₁.appLE _ _ h1).hom x = (g₂.appLE _ _ h2).hom x := by
      rintro _ _ rfl _ _ _; rfl
    refine k1.trans (Eq.trans ?_ k2.symm)
    exact k3 _ _ e _ _ b
  let θ1 : ((preRes φ s').comp m).G ⟶ ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  let θ2 : ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).G ⟶
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).G :=
    { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
  have h1 : ∀ T b, ((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T
      (mp (OAff s') (θ1.app T) b) = ((preRes φ s').comp m).α T b := fun T b ↦ by
    exact congrArg (((pairPull w').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T) (mp_id (OAff s') _ b)
  have h2 : ∀ T b, (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T
      (mp (OAff q') (θ2.app T) b) = ((pairRes ψ' q').comp (CoefMap.restrict (OPair ψ' q') Φ)).α T b :=
    fun T b ↦ by
      exact congrArg ((CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).α T) (mp_id (OAff q') _ b)
  refine ⟨fun f x hr ↦ ?_, fun v z hr ↦ ?_⟩
  · obtain ⟨c0, hc0, hcl⟩ := (H.1 f x).1 hr
    refine ⟨m.pullbackOneCocycle c0, fun a b u ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleOne_apply, hc0]; exact hα b _
    · rw [← CoefMap.pullCohomologyOne_class, hcl, ← CoefMap.pullCohomologyOne_comp]
      exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ1 h1 x).trans ((CoefMap.pullCohomologyOne_comp _ _ x).trans
        ((congrArg _ (isPullO_pullHO1 w' x)).trans ((CoefMap.pullCohomologyOne_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ2 h2 _))))
  · obtain ⟨c0, hc0, hcl⟩ := (H.2.1 v z).1 hr
    have k : (pairRes ψ' q').pull2 (pullHO2 w' z) = (pairPull w').pull2 z :=
      (LinearEquiv.ofBijective _ (pairRes_pull2_bijective ψ' q')).apply_symm_apply _
    refine ⟨m.pullbackTwoCocycle c0, fun a b d u u' ↦ ?_, ?_⟩
    · rw [CoefMap.pullCocycleTwo_apply, hc0]; exact hα d _
    · rw [← CoefMap.pullCohomologyTwo_class, hcl, ← CoefMap.pullCohomologyTwo_comp]
      exact (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ1 h1 z).trans ((CoefMap.pullCohomologyTwo_comp _ _ z).trans
        ((congrArg _ k.symm).trans ((CoefMap.pullCohomologyTwo_comp _ _ _).symm.trans
          (CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ2 h2 _))))

end GlobalTheory.AbCoh
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem preRes_bijective : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (φ : X' ⟶ X) [IsClosedImmersion φ] (s' : X' ⟶ Sp R'), Function.Bijective (preRes φ s').pull1 ∧ Function.Bijective (preRes φ s').pull2 ∧ (CohomZeroIsConstants (OAff s') → CohomZeroIsConstants (OPre φ s')) := by
  intro R' _ X X' φ _ s'
  have hB : ∀ {U : TopologicalSpace.Opens X} {x : X}, x ∈ U → ∃ U' ∈ X.affineOpens, x ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
  refine GlobalTheory.T.structureSheafCohomology_basis_bijective R' X' s' X.affineOpens (preU φ) (preU_mono φ) ?_ ?_
  · intro U x hx
    obtain ⟨W, hW, hWU⟩ := (φ.isClosedEmbedding).isInducing.isOpen_iff.mp U.1.2
    have hxW : φ.base x ∈ W := by
      have : x ∈ φ.base ⁻¹' W := by rw [hWU]; exact hx
      exact this
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := ⟨W, hW⟩) hxW
    refine ⟨⟨V, hV⟩, hxV, ?_⟩
    intro y hy
    have : y ∈ φ.base ⁻¹' W := hVW hy
    rw [hWU] at this
    exact this
  · intro a b x ha hb
    obtain ⟨V, hV, hxV, hVW⟩ := hB (U := a.1 ⊓ b.1) ⟨ha, hb⟩
    exact ⟨⟨V, hV⟩, fun y hy ↦ (hVW hy).1, fun y hy ↦ (hVW hy).2, hxV⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset


theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  first | exact @GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | exact GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | (intros; apply GlobalTheory.CechPoset.Φ_ext_eq_pullCoef <;> assumption)
end
