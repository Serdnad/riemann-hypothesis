module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle393
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Unramified.LocalStructure
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConstFibreFree

theorem finrank_tensor_tower (O k K M : Type) [CommRing O] [Field k] [Field K] [Algebra O k]
    [Algebra O K] [Algebra k K] [IsScalarTower O k K] [AddCommGroup M] [Module O M]
    [Module.Finite O M] :
    Module.finrank K (K ⊗[O] M) = Module.finrank k (k ⊗[O] M) := by
  rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange O k K K M).finrank_eq]
  exact Module.finrank_baseChange

theorem fibreDim_closedPoint (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    fibreDim M (IsLocalRing.closedPoint O) =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] M) := by
  let q := IsLocalRing.closedPoint O
  let φ : IsLocalRing.ResidueField O →+* q.asIdeal.ResidueField :=
    Ideal.Quotient.lift _ (algebraMap O q.asIdeal.ResidueField) fun a ha => by
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]; exact ha
  letI : Algebra (IsLocalRing.ResidueField O) q.asIdeal.ResidueField := φ.toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.Quotient.lift_mk _ _ _).symm
  exact finrank_tensor_tower O _ _ M

theorem exists_one_tmul (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    (y : IsLocalRing.ResidueField O ⊗[O] M) : ∃ m : M, (1 : IsLocalRing.ResidueField O) ⊗ₜ[O] m = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul c m =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  | add y z hy hz =>
    obtain ⟨m₁, h₁⟩ := hy
    obtain ⟨m₂, h₂⟩ := hz
    exact ⟨m₁ + m₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩

theorem nonempty_equiv_fin (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type)
    [AddCommGroup M] [Module O M] [Module.Finite O M] (n : ℕ)
    (h : ∀ q : PrimeSpectrum O, fibreDim M q = n) : Nonempty (M ≃ₗ[O] (Fin n → O)) := by
  let k := IsLocalRing.ResidueField O
  have hk : Module.finrank k (k ⊗[O] M) = n :=
    (fibreDim_closedPoint O M).symm.trans (h _)
  let b : Module.Basis (Fin n) k (k ⊗[O] M) := Module.finBasisOfFinrankEq k _ hk
  choose f hf using fun i => exists_one_tmul O M (b i)
  let g : (Fin n → O) →ₗ[O] M := Fintype.linearCombination O f
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis f b hf
  have hinj : Function.Injective g := by
    let q₀ : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
    let K := q₀.asIdeal.ResidueField
    have hK : Module.finrank K (K ⊗[O] M) = n := h q₀
    let gK := g.baseChange K
    have hgK : Function.Surjective gK := LinearMap.lTensor_surjective K hg
    have hdim : Module.finrank K (K ⊗[O] (Fin n → O)) = Module.finrank K (K ⊗[O] M) := by
      rw [hK, Module.finrank_baseChange, Module.finrank_fin_fun]
    have hgKi : Function.Injective gK :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hgK
    have hO : Function.Injective (algebraMap O K) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : gK ((1 : K) ⊗ₜ x) = 0 := by simp [gK, hx]
    have h2 : (1 : K) ⊗ₜ[O] x = 0 := hgKi (h1.trans (map_zero gK).symm)
    have h3 := congrArg (TensorProduct.piScalarRight O K K (Fin n)) h2
    funext i
    have h4 := congrFun h3 i
    simp at h4
    exact hO (by simpa using h4)
  exact ⟨(LinearEquiv.ofBijective g ⟨hinj, hg⟩).symm⟩

theorem projective_and_rankAtStalk_of_fibreDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
      [Module.Finite O M] (n : ℕ), (∀ q : PrimeSpectrum O, fibreDim M q = n) →
      Module.Projective O M ∧ ∀ q : PrimeSpectrum O, Module.rankAtStalk M q = n := by
  intro O _ _ _ M _ _ _ n h
  obtain ⟨e⟩ := nonempty_equiv_fin O M n h
  haveI : Module.Free O M := Module.Free.of_equiv e.symm
  refine ⟨inferInstance, fun q => ?_⟩
  rw [Module.rankAtStalk_eq]
  exact h q

end GlobalTheory.ConstFibreFree
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

theorem res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (j : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ j) x = Sec.res k (Sec.res j x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_smul {V U : Scheme.{0}} (j : V ⟶ U) (c : R) (x : Sec F U) :
    Sec.res j ((ULift.up c : ULift.{1} R) • x) = (ULift.up c : ULift.{1} R) • Sec.res j x :=
  map_smul _ _ _

theorem res_add {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x + y) = Sec.res j x + Sec.res j y := map_add _ _ _

theorem res_sub {V U : Scheme.{0}} (j : V ⟶ U) (x y : Sec F U) :
    Sec.res j (x - y) = Sec.res j x - Sec.res j y := map_sub _ _ _

theorem sep {U : Scheme.{0}} (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U) (he : ∀ i, Etale (j i))
    (hc : ∀ u : U, ∃ i v, j i v = u) (x y : Sec F U) (h : ∀ i, Sec.res (j i) x = Sec.res (j i) y) : x = y :=
  sub_eq_zero.1 ((GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U ι V j he hc).1 (x - y) (fun i => by rw [res_sub, h i, sub_self]))

theorem sec_empty {V : Scheme.{0}} [IsEmpty V] (x y : Sec F V) : x = y :=
  sep PEmpty (fun _ => V) (fun _ => 𝟙 V) (fun _ => inferInstance) (fun u => isEmptyElim u) x y (fun i => i.elim)

def fib {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) : V.Opens :=
  ⟨ψ ⁻¹' {ψ v}, ψ.isLocallyConstant.isOpen_fiber _⟩

theorem fib_apply {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (v : V) (w : (fib ψ v).toScheme) :
    ψ ((fib ψ v).ι w) = ψ v := by
  have h := (Scheme.Opens.range_ι (fib ψ v)).subset ⟨w, rfl⟩
  exact h

theorem fib_cov {V : Scheme.{0}} {α : Type} (ψ : LocallyConstant V α) (u : V) :
    ∃ (i : V) (w : (fib ψ i).toScheme), (fib ψ i).ι w = u := by
  have h : u ∈ Set.range (fib ψ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, hw⟩ := h
  exact ⟨u, w, hw⟩

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

def IsMul {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (j : V ⟶ U) (c : R), (∀ v, φ (j v) = c) →
    Sec.res j x = (ULift.up c : ULift.{1} R) • Sec.res (j ≫ s) g

theorem isMul_of_fib {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x : Sec F U)
    (h : ∀ u, Sec.res (fib φ u).ι x = (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) : IsMul s g φ x := by
  intro V j c hc
  by_cases hV : IsEmpty V
  · exact sec_empty _ _
  obtain ⟨v⟩ := not_isEmpty_iff.1 hV
  have H : Set.range j ⊆ Set.range (fib φ (j v)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change φ (j w) = φ (j v)
    rw [hc w, hc v]
  have hf := IsOpenImmersion.lift_fac (fib φ (j v)).ι j H
  rw [← hf, res_comp, h, res_smul, ← res_comp, hc v, Category.assoc]

theorem isMul_unique {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g φ y) : x = y :=
  sep U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance) (fib_cov φ) x y
    (fun u => by rw [hx _ _ (φ u) (fib_apply φ u), hy _ _ (φ u) (fib_apply φ u)])

theorem isMul_exists {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    ∃ x, IsMul s g φ x := by
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family R F U U (fun u => (fib φ u).toScheme) (fun u => (fib φ u).ι) (fun _ => inferInstance)
    (fib_cov φ)).2 (fun u => (ULift.up (φ u) : ULift.{1} R) • Sec.res ((fib φ u).ι ≫ s) g) (by
      intro i k
      rw [res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, pullback.condition]
      by_cases hP : IsEmpty (pullback (fib φ i).ι (fib φ k).ι : Scheme.{0})
      · exact sec_empty _ _
      obtain ⟨p⟩ := not_isEmpty_iff.1 hP
      have e : φ i = φ k := by
        rw [← fib_apply φ i (pullback.fst (fib φ i).ι (fib φ k).ι p), ← fib_apply φ k (pullback.snd (fib φ i).ι (fib φ k).ι p),
          ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [e])
  exact ⟨x, isMul_of_fib s g φ x hx⟩

theorem isMul_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) (x y : Sec F U)
    (hx : IsMul s g φ x) (hy : IsMul s g ψ y) : IsMul s g (φ + ψ) (x + y) := by
  intro V j c hc
  let χ : LocallyConstant V (R × R) :=
    ⟨fun v => (φ (j v), ψ (j v)), ((φ.comap j.base.hom).isLocallyConstant.comp₂ (ψ.comap j.base.hom).isLocallyConstant Prod.mk)⟩
  refine sep V (fun v => (fib χ v).toScheme) (fun v => (fib χ v).ι) (fun _ => inferInstance) (fib_cov χ) _ _ (fun v => ?_)
  have h1 : ∀ w, φ (((fib χ v).ι ≫ j) w) = φ (j v) := fun w => congrArg Prod.fst (fib_apply χ v w)
  have h2 : ∀ w, ψ (((fib χ v).ι ≫ j) w) = ψ (j v) := fun w => congrArg Prod.snd (fib_apply χ v w)
  rw [← res_comp, res_add, hx _ _ _ h1, hy _ _ _ h2, res_smul, ← res_comp, ← add_smul, ← hc v]
  rfl

end GlobalTheory.EtC.GenLC

namespace GlobalTheory.EtC.GenLC

variable {R : Type} [CommRing R] {F : Shv R}

noncomputable def mulSec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) : Sec F U :=
  (isMul_exists s g φ).choose

theorem mulSec_spec {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ : LocallyConstant U R) :
    IsMul s g φ (mulSec s g φ) := (isMul_exists s g φ).choose_spec

theorem mulSec_add {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (φ ψ : LocallyConstant U R) :
    mulSec s g (φ + ψ) = mulSec s g φ + mulSec s g ψ :=
  isMul_unique s g _ _ _ (mulSec_spec s g _) (isMul_add s g φ ψ _ _ (mulSec_spec s g φ) (mulSec_spec s g ψ))

theorem coeff_eq {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U)
    {V₁ V₂ : Scheme.{0}} (j₁ : V₁ ⟶ U) (j₂ : V₂ ⟶ U) (c₁ c₂ : R)
    (h₁ : Sec.res j₁ x = (ULift.up c₁ : ULift.{1} R) • Sec.res (j₁ ≫ s) g)
    (h₂ : Sec.res j₂ x = (ULift.up c₂ : ULift.{1} R) • Sec.res (j₂ ≫ s) g) (v₁ : V₁) (v₂ : V₂) (hv : j₁ v₁ = j₂ v₂) :
    c₁ = c₂ := by
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v₁ v₂ hv
  have e : Sec.res (pullback.fst j₁ j₂) (Sec.res j₁ x) = Sec.res (pullback.snd j₁ j₂) (Sec.res j₂ x) := by
    rw [← res_comp, ← res_comp, pullback.condition]
  rw [h₁, h₂, res_smul, res_smul, ← res_comp, ← res_comp, ← Category.assoc, ← Category.assoc, ← pullback.condition] at e
  have h0 : (ULift.up (c₁ - c₂) : ULift.{1} R) • Sec.res ((pullback.fst j₁ j₂ ≫ j₁) ≫ s) g = 0 := by
    have hu : (ULift.up (c₁ - c₂) : ULift.{1} R) = ULift.up c₁ - ULift.up c₂ := rfl
    rw [hu, sub_smul, e, sub_self]
  exact sub_eq_zero.1 ((hg _ _).2 (c₁ - c₂) ⟨p⟩ h0)

theorem mulSec_inj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (φ : LocallyConstant U R)
    (h : mulSec s g φ = 0) : φ = 0 := by
  ext u
  have e := mulSec_spec s g φ _ (fib φ u).ι (φ u) (fib_apply φ u)
  rw [h] at e
  have hu : u ∈ Set.range (fib φ u).ι := by rw [Scheme.Opens.range_ι]; exact rfl
  obtain ⟨w, -⟩ := hu
  exact (hg (fib φ u).toScheme ((fib φ u).ι ≫ s)).2 (φ u) ⟨w⟩ (by rw [← e]; exact map_zero _)

theorem mulSec_surj {S U : Scheme.{0}} (s : U ⟶ S) (g : Sec F S) (hg : Gen F S g) (x : Sec F U) :
    ∃ φ, mulSec s g φ = x := by
  choose V j v c he hv hx₀ using (hg U s).1 x
  have hx : ∀ u, Sec.res (j u) x = (ULift.up (c u) : ULift.{1} R) • Sec.res (j u ≫ s) g := hx₀
  have hconst : ∀ u, ∀ u' ∈ Set.range (j u), c u' = c u := by
    rintro u _ ⟨w, rfl⟩
    exact coeff_eq s g hg x (j (j u w)) (j u) _ _ (hx _) (hx u) _ w (hv _)
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (j u), (j u).isOpenMap.isOpen_range, ⟨v u, hv u⟩, hconst u⟩
  refine ⟨⟨c, hlc⟩, isMul_unique s g _ _ _ (mulSec_spec s g _) ?_⟩
  intro W k a ha
  refine sep W (fun w => (pullback (j (k w)) k : Scheme.{0})) (fun w => pullback.snd (j (k w)) k)
    (fun _ => inferInstance) (fun w => ?_) _ _ (fun w => ?_)
  · obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (v (k w)) w (hv (k w))
    exact ⟨w, p, hp⟩
  · have hc : c (k w) = a := ha w
    rw [← res_comp, ← pullback.condition, res_comp, hx, res_smul, ← res_comp, res_smul, ← res_comp, hc,
      ← Category.assoc, ← Category.assoc, pullback.condition]

end GlobalTheory.EtC.GenLC


open GlobalTheory.EtC.GenLC in
theorem GlobalTheory.EtC.gen_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∃ e : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R ≃+ Sec F U, (∀ U s (c : R), e U s (LocallyConstant.const U c) = (ULift.up c : ULift.{1} R) • Sec.res s g) ∧ ∀ (V U : Scheme.{0}) (j : V ⟶ U) (s : U ⟶ S) (φ : LocallyConstant U R), Sec.res j (e U s φ) = e V (j ≫ s) (φ.comap j.base.hom) := by
  intro R _ F S g hg
  let m : ∀ (U : Scheme.{0}) (s : U ⟶ S), LocallyConstant U R →+ Sec F U := fun U s =>
    AddMonoidHom.mk' (mulSec s g) (mulSec_add s g)
  refine ⟨fun U s => AddEquiv.ofBijective (m U s)
    ⟨(injective_iff_map_eq_zero (m U s)).2 (fun φ h => mulSec_inj s g hg φ h), mulSec_surj s g hg⟩, ?_, ?_⟩
  · intro U s c
    show mulSec s g (LocallyConstant.const U c) = _
    refine isMul_unique s g _ _ _ (mulSec_spec s g _) ?_
    intro V j a ha
    rw [res_smul, ← res_comp]
    by_cases hV : IsEmpty V
    · exact sec_empty _ _
    obtain ⟨v⟩ := not_isEmpty_iff.1 hV
    have hca : c = a := ha v
    rw [hca]
  · intro V U j s φ
    show Sec.res j (mulSec s g φ) = mulSec (j ≫ s) g (φ.comap j.base.hom)
    refine isMul_unique (j ≫ s) g _ _ _ ?_ (mulSec_spec (j ≫ s) g _)
    intro W k a ha
    rw [← res_comp, mulSec_spec s g φ W (k ≫ j) a ha, Category.assoc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem wExact_term_HC (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T]
    (Φ : T ⥤ Spcᵒᵖ) (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X)
    (h : Hyp R Φ a) (n : ℤ) : WExact (term (Φ ⋙ HC R F) n) a := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  exact GlobalTheory.EtC.WExactProd.wexact_of_prod T U X a ℕ
    (fun k => Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)))
    (term (Φ ⋙ HC R F) n) (fun k => Functor.whiskerLeft Φ (π k)) (fun V => hπ (Φ.obj V))
    (fun k => wExact_preadditiveYoneda_of_injective R T (Φ ⋙ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op)
      U X a ((res R F).X (n - k)) ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).1 (n - k)) (h (op (SimplexCategory.mk k))))

end GlobalTheory.EtC
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IndEtaleAtPrime

theorem isIndEtale_of_etale_atPrime (R C : Type) [CommRing R] [CommRing C] (P : Ideal R) [P.IsPrime]
    [Algebra (Localization.AtPrime P) C] [Algebra.Etale (Localization.AtPrime P) C] :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap (Localization.AtPrime P) C).comp
      (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := GlobalTheory.IndEtFactorLoc.constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C
  let Re : Type := Localization.Away j.e
  letI : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  letI : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  letI : Algebra Re Aj := instA
  haveI : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  haveI : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  haveI : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  haveI hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  letI rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  letI : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  haveI hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  letI : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  haveI : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  haveI : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  letI : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)

theorem indEt_of_indEt_atPrime : ∀ (B O : Type) [CommRing B] [CommRing O] (P : Ideal B) [P.IsPrime]
    [Algebra (Localization.AtPrime P) O] [Algebra B O] [IsScalarTower B (Localization.AtPrime P) O],
    IndEt (Localization.AtPrime P) O → IndEt B O := by
  intro B O _ _ P _ _ _ _ h
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  unfold IndEt GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  refine ⟨J, inferInstance, inferInstance, D,
    (Functor.const J).map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime P))) ≫ t, s, hs,
    fun i => ⟨?_, ?_⟩⟩
  · letI : Algebra (Localization.AtPrime P) (D.obj i) := (t.app i).hom.toAlgebra
    haveI : Algebra.Etale (Localization.AtPrime P) (D.obj i) := (hj i).1
    exact isIndEtale_of_etale_atPrime B (D.obj i) P
  · have h2 := (hj i).2
    show CommRingCat.ofHom (algebraMap B (Localization.AtPrime P)) ≫ t.app i ≫ s.app i = _
    rw [h2]
    ext x
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime P) O x).symm

end GlobalTheory.IndEtaleAtPrime

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cofiltered_limit_affine_etale_of_isStalk : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  intro S O _ s hs
  obtain ⟨_, A, _, _, j, hj, hind, rfl⟩ := hs
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hind
  let G : Jᵒᵖ ⥤ Over S :=
    { obj := fun k => Over.mk (Spec.map (D.obj k.unop).hom ≫ j)
      map := fun {k l} f => Over.homMk (Spec.map (D.map f.unop).right) (by
        dsimp
        rw [← Category.assoc, ← Spec.map_comp, Under.w])
      map_id := fun k => by ext1; simp
      map_comp := fun f g => by ext1; simp [Spec.map_comp] }
  let π : (Functor.const Jᵒᵖ).obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j)) ⟶ G :=
    { app := fun k => Over.homMk (Spec.map (ι.app k.unop).right) (by
        dsimp [G]
        rw [← Category.assoc, ← Spec.map_comp, Under.w (ι.app k.unop)]
        rfl)
      naturality := fun k l f => by
        ext1
        change (𝟙 _ ≫ Spec.map (ι.app l.unop).right) = Spec.map (ι.app k.unop).right ≫ Spec.map (D.map f.unop).right
        rw [Category.id_comp, ← Spec.map_comp]
        congr 1
        have := congrArg (fun m => Under.Hom.right m) (ι.naturality f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Under.comp_right] at this
        exact this.symm }
  haveI : IsConnected J := IsFiltered.isConnected J
  haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G, π, ⟨?_⟩, fun k => ⟨?_, ?_⟩⟩
  · apply isLimitOfReflects (Over.forget S)
    have h1 := isColimitOfPreserves (Under.forget (CommRingCat.of A)) hc
    have h2 := isLimitOfPreserves Scheme.Spec h1.op
    exact h2
  · dsimp [G]; infer_instance
  · dsimp [G]
    have : Etale (Spec.map (D.obj k.unop).hom) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (het k.unop)
    infer_instance

end GlobalTheory.EtC
end
