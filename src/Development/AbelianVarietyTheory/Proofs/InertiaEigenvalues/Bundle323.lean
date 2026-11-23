module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle091
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle245
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
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
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.HkGoodStable

theorem hkF_mem_V0 : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  intro D hC i hi j hj b k P hk x hx
  have hc : ∀ g z, D.nexp.actG i j b g (D.nexp.hkF i j b k P z) = D.nexp.hkF i j b k P (D.nexp.actG i j b g z) :=
    fun g z => LinearMap.congr_fun (hC i hi b j hj g k P hk) z
  have hcomm : ∀ a, Commute (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
      (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) a) (D.nexp.hkF i j b k P) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.lift_of]
      exact LinearMap.ext fun z => hc g z
    | add a a' ha ha' => rw [map_add (f := _)]; exact ha.add_left ha'
    | smul c a ha => rw [map_smul]; exact ha.smul_left c
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨D.nexp.hkF i j b k P y, ?_, ?_⟩
  · simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe] at hy ⊢
    intro u
    have h := hy u
    rw [sub_eq_zero] at h ⊢
    rw [hc, h, map_smul]
  · exact LinearMap.congr_fun (hcomm (D.nexp.eAlg i b)) y

end GlobalTheory.HkGoodStable
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

theorem selMaps_res_map {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem selMaps_map_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (selMaps_res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']

theorem localConditionAboveL_coeffMap_functorial (f : B →ₗ[Λ] B') (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) : h1MapSubgroup ρ κ (DecV N v) f x ∈ bkOn bkP i ρ κ B' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology
        (fun g m => repOn_map ρ κ f g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → B) g a) = _
      rw [hz, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem selmerClass_coeffMap_mem_selmer (f : B →ₗ[Λ] B') (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : h1Map ρ κ f x ∈ selOn bkP i ρ κ B' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (selMaps_res_map (repOn ρ κ B) (repOn ρ κ B') (f.compLeft (Fin r)) continuous_of_discreteTopology
    (repOn_map ρ κ f) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact localConditionAboveL_coeffMap_functorial bkP i ρ κ f v _ hv
  · exact Submodule.mem_top
  · exact selMaps_map_ur _ _ _ _ _ _ _ hv

theorem selMaps (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) : SelMaps bkP i s κ Q := by
  intro B B' _ _ _ _ _ _ _ _ f
  rintro _ ⟨x, hx, rfl⟩
  exact selmerClass_coeffMap_mem_selmer bkP i _ κ f Q x hx

end GlobalTheory.SelFun

end
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SplitFrobDense

theorem exists_conj_ne {R : Ranks} (H : Host R) :
    ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem frobDense : ∀ D : D7, GlobalTheory.TwSys.Cheb → FrobDense D := by
  classical
  intro D hC T hT
  rw [dense_iff_inter_open]
  rintro V hV ⟨g, hg⟩
  have : IsGalois D.host.E D.nd.Om := {}
  have hn : (fun u : G D.host.E D.nd.Om => u * g) ⁻¹' V ∈ nhds (1 : G D.host.E D.nd.Om) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal D.host.E D.nd.Om _).1 hn
  have hgal : IsGalois D.host.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne D.host
  have f1 : {v : PlE D.host | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC D.host.E D.nd.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ hT.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl D.host v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right] at this
  exact ⟨σ, this, v, h2, hsplit, B, hB, hσ⟩

end GlobalTheory.SplitFrobDense
end

section

open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Level

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ]

def IsMin (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (A : ModuleCat.{0} Λ) (x : F.obj A) : Prop :=
  ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : A ⟶ B, (F.map φ).hom x = 0 → φ = 0

def LeftEx (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) : Prop :=
  ∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom

theorem map_map (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) {A B C : ModuleCat.{0} Λ} (f : A ⟶ B) (g : B ⟶ C)
    (x : F.obj A) : (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]; rfl

theorem exists_min (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (hF : LeftEx F) (A : ModuleCat.{0} Λ) [Finite A]
    (hA : Tors Λ A) (x : F.obj A) :
    ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧ (F.map f).hom z = x ∧
      IsMin F C z := by
  classical
  have hex : ∃ m : ℕ, ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧
      (F.map f).hom z = x ∧ Nat.card C = m :=
    ⟨_, A, 𝟙 A, x, Function.injective_id, by rw [F.map_id]; rfl, rfl⟩
  obtain ⟨C, f, z, hf, hz, hm⟩ := Nat.find_spec hex
  refine ⟨C, f, z, hf, hz, fun B hB φ hφ => ?_⟩
  haveI : Finite C := Finite.of_injective _ hf
  have hC : Tors Λ C := fun c => by
    obtain ⟨n, hn⟩ := hA (f.hom c)
    exact ⟨n, fun r hr => hf (by rw [map_smul, hn r hr, map_zero])⟩
  obtain ⟨-, h2⟩ := hF (ModuleCat.of Λ (LinearMap.ker φ.hom)) C B hC hB
    (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype) φ Subtype.val_injective
    (LinearMap.exact_subtype_ker_map φ.hom)
  obtain ⟨w, hw⟩ := (h2 z).1 hφ
  have hle : Nat.find hex ≤ Nat.card (LinearMap.ker φ.hom) :=
    Nat.find_min' hex ⟨ModuleCat.of Λ (LinearMap.ker φ.hom),
      ModuleCat.ofHom (LinearMap.ker φ.hom).subtype ≫ f, w, hf.comp Subtype.val_injective,
      by rw [← map_map, hw, hz], rfl⟩
  rw [← hm] at hle
  have hbij : Function.Bijective (LinearMap.ker φ.hom).subtype :=
    Function.Injective.bijective_of_nat_card_le Subtype.val_injective hle
  ext c
  obtain ⟨k, rfl⟩ := hbij.2 c
  exact k.2

theorem card_le_of_min [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive]
    (hfin : Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)))) (n : ℕ) :
    ∃ N : ℕ, ∀ (A : ModuleCat.{0} Λ) (x : F.obj A), Finite A →
      (∀ r ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, r • y = 0) → IsMin F A x → Nat.card A ≤ N := by
  set c := Nat.card (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) with hc
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) := ‹Finite (IsLocalRing.ResidueField Λ)›
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  refine ⟨Nat.card (Fin c → Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n), fun A x hA hn hmin => ?_⟩
  have hk : Tors Λ (IsLocalRing.ResidueField Λ) := fun b => ⟨1, fun r hr => by
    rw [pow_one] at hr
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff r).2 hr, zero_mul]⟩
  have hinj : Function.Injective (fun φ : A →ₗ[Λ] IsLocalRing.ResidueField Λ =>
      (F.map (ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).hom x) := by
    intro φ ψ h
    have := hmin (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) hk
      ((ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) - ModuleCat.ofHom ψ) (by
        rw [F.map_sub]
        exact sub_eq_zero.2 h)
    have h2 := sub_eq_zero.1 this
    exact congrArg ModuleCat.Hom.hom h2
  have h1 : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ c := Nat.card_le_card_of_injective _ hinj
  have h2 : c ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ c :=
    (Nat.lt_pow_self Finite.one_lt_card).le
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ A c (h1.trans h2)
  let p : Fin c → (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) →ₗ[Λ] A := fun i =>
    (IsLocalRing.maximalIdeal Λ ^ n).liftQ (LinearMap.toSpanSingleton Λ A (v i)) (fun r hr => hn r hr _)
  refine Nat.card_le_card_of_surjective (fun t => ∑ i, p i (t i)) (fun a => ?_)
  have ha : a ∈ Submodule.span Λ (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 ha
  exact ⟨fun i => Submodule.Quotient.mk (t i), rfl⟩

theorem level : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  classical
  intro Λ _ _ _ _ F _ _ hF hfin n
  obtain ⟨N, hN⟩ := card_le_of_min F hfin n
  let P : ℕ → Prop := fun m => ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧
    (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧ IsMin F M ξ ∧ Nat.card M = m
  have h0 : P (Nat.card (ModuleCat.of Λ PUnit)) :=
    ⟨ModuleCat.of Λ PUnit, 0, inferInstanceAs (Finite PUnit), fun _ _ _ => rfl, fun B _ φ _ => by
      ext c
      exact map_zero φ.hom, rfl⟩
  have hle : ∀ m, P m → m ≤ N := by
    rintro m ⟨M, ξ, h1, h2, h3, rfl⟩
    exact hN M ξ h1 h2 h3
  obtain ⟨M, ξ, hM, hMn, hmin, hcard⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec (hle _ h0) h0
  refine ⟨M, ξ, hM, hMn, hmin, fun B hB hBn η => ?_⟩
  let A : ModuleCat.{0} Λ := ModuleCat.of Λ (M × B)
  haveI : Finite A := inferInstanceAs (Finite (M × B))
  have hAn : ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, x • y = 0 := fun r hr y =>
    Prod.ext (hMn r hr y.1) (hBn r hr y.2)
  let i1 : M ⟶ A := ModuleCat.ofHom (LinearMap.inl Λ M B)
  let i2 : B ⟶ A := ModuleCat.ofHom (LinearMap.inr Λ M B)
  let q1 : A ⟶ M := ModuleCat.ofHom (LinearMap.fst Λ M B)
  let q2 : A ⟶ B := ModuleCat.ofHom (LinearMap.snd Λ M B)
  have e11 : i1 ≫ q1 = 𝟙 M := rfl
  have e22 : i2 ≫ q2 = 𝟙 B := rfl
  have e12 : i1 ≫ q2 = 0 := rfl
  have e21 : i2 ≫ q1 = 0 := rfl
  obtain ⟨C, f, z, hf, hz, hC⟩ := exists_min F hF A (fun a => ⟨n, fun r hr => hAn r hr a⟩)
    ((F.map i1).hom ξ + (F.map i2).hom η)
  have hz1 : (F.map (f ≫ q1)).hom z = ξ := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e11, e21, F.map_id, F.map_zero]
    exact add_zero _
  have hz2 : (F.map (f ≫ q2)).hom z = η := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e12, e22, F.map_id, F.map_zero]
    exact zero_add _
  haveI hCf : Finite C := Finite.of_injective _ hf
  set g := f ≫ q1 with hg
  have hsurj : Function.Surjective g.hom := by
    have := hmin (ModuleCat.of Λ (M ⧸ LinearMap.range g.hom)) (fun b => ⟨n, fun r hr => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [← Submodule.Quotient.mk_smul, hMn r hr, Submodule.Quotient.mk_zero]⟩)
      (ModuleCat.ofHom (LinearMap.range g.hom).mkQ) (by
        have e : g ≫ ModuleCat.ofHom (LinearMap.range g.hom).mkQ = 0 := by
          ext c
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩
        rw [← hz1, map_map, e, F.map_zero]
        rfl)
    intro m
    have h3 : (LinearMap.range g.hom).mkQ m = 0 :=
      congrArg (fun φ : M ⟶ ModuleCat.of Λ (M ⧸ LinearMap.range g.hom) => φ.hom m) this
    exact (Submodule.Quotient.mk_eq_zero _).1 h3
  have hPC : P (Nat.card C) := ⟨C, z, hCf, fun r hr y => hf (by rw [map_smul, hAn r hr, map_zero]), hC, rfl⟩
  have hcle : Nat.card C ≤ Nat.card M := hcard ▸ Nat.le_findGreatest (hle _ hPC) hPC
  have hbij : Function.Bijective g.hom := hsurj.bijective_of_nat_card_le hcle
  let e := LinearEquiv.ofBijective g.hom hbij
  refine ⟨(ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) ≫ f ≫ q2, ?_⟩
  have e3 : g ≫ (ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) = 𝟙 C := by
    ext c
    exact e.symm_apply_apply c
  rw [← hz1, map_map, ← Category.assoc, e3, Category.id_comp, hz2]

end GlobalTheory.SelFun.Level
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem zeta_Y'_fine_bound : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hηH hl y hy
  obtain ⟨y₀, ⟨hy₀, -⟩, rfl⟩ := hy
  have hy₀' : E K l e ^ η • y₀ ∈ D.M := hy₀
  show ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta ((X : K⟦X⟧) ^ e • y₀) = _
  obtain ⟨r, hr, hT⟩ := GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin O K l e a ι η H D y₀ hη hηH hl hy₀'
  obtain ⟨w₁, hw₁, hB⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀' 0
  obtain ⟨s, hs, f, hf, hD⟩ := GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule O K l e a ι D.toPhiMod (10 * H) (by omega) w₁ hw₁
  have hIC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH (by omega)
  obtain ⟨p₁, hp₁, f₁, hf₁, rfl⟩ := hIC.1 s hs
  obtain ⟨p₂, hp₂, f₂, hf₂, rfl⟩ := hIC.1 r hr
  have hsm : ∀ {R : Type} [Semiring R] [Module R (Vec K a ι)] (W : Submodule R (Vec K a ι)) (k : ℕ)
      {v : Vec K a ι}, v ∈ W → (l : K) ^ k • v ∈ W := fun W k v hv => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv _
  refine ⟨p₂ - (l : K) ^ (3 * H - 2 * η) • p₁, sub_mem hp₂ (hsm _ _ hp₁),
    (l : K) ^ (l - 11 * H) • f₂ - (l : K) ^ (2 * H - 2 * η) • ((l : K) ^ (l - 10 * H) • f₁ + f),
    sub_mem (hsm _ _ hf₂) (hsm _ _ (add_mem (hsm _ _ hf₁) hf)), ?_⟩
  simp only [zero_add, pow_one, zero_mul, add_zero, one_mul] at hB
  rw [hD] at hB
  have hl0 : (l : K) ≠ 0 := l_ne_zero l
  have e1 : l - 10 * H = (l - 14 * H) + (3 * H - 2 * η) + (H + 2 * η) := by omega
  have e2 : l - 11 * H = (l - 14 * H) + (2 * H - 2 * η) + (H + 2 * η) := by omega
  have e3 : (l : K) ^ (3 * H) = (l : K) ^ (2 * H - 2 * η) * (l : K) ^ (H + 2 * η) := by
    rw [← pow_add]; congr 1; omega
  rw [e1] at hB
  rw [e1, e2, e3]
  have hz := eq_sub_of_add_eq hT
  rw [hz]
  generalize l - 14 * H = A at *
  generalize 3 * H - 2 * η = B at *
  generalize 2 * H - 2 * η = Dd at *
  generalize H + 2 * η = Cc at *
  generalize (l : K) = x at *
  have hL : D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (x ^ Cc)⁻¹ • (x ^ (A + B + Cc) • (p₁ + f₁) + f) := by
    rw [← hB, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  rw [hL]
  match_scalars <;> field_simp <;> ring

end GlobalTheory.BK
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  first | exact @GlobalTheory.Models.SubModel.model_pre | exact GlobalTheory.Models.SubModel.model_pre | (intros; apply GlobalTheory.Models.SubModel.model_pre <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.character_model_exponents_signs_senWeight : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  first | exact @GlobalTheory.Models.CharSign.model_char_sign | exact GlobalTheory.Models.CharSign.model_char_sign | (intros; apply GlobalTheory.Models.CharSign.model_char_sign <;> assumption)
end
