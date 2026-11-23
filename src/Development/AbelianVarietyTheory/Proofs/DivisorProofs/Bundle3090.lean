module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_invariant_maps_affineOpen_smoothModel : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  first | exact @GlobalTheory.Mum.exists_invariant_maps_of_affine_open | exact GlobalTheory.Mum.exists_invariant_maps_of_affine_open | (intros; apply GlobalTheory.Mum.exists_invariant_maps_of_affine_open <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Izumi

theorem small_mod_principal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  intro o Ω _ _ _ _ M hn U hU x hx f hf hf0
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x
  have hB := GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span o Ω M hn U hU x hx f hf hf0
  choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩
    (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB
  refine ⟨C, fun e F hF => ?_⟩
  have hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e := hC e (mem_smallIdeal.2 hF)
  obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := Ideal.span_eq (maximalIdeal (M.O x))
  refine ⟨a, b, rfl, ?_⟩
  rw [hm]
  exact hb

end GlobalTheory.Izumi
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwNorm

open GlobalTheory.TwFac

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_normalised (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a]
    (hh : ∀ y, D.c (h y) = D.c y ≫ a) (n j : ℤ) (mu β' : D.X)
    (g : ∀ y : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c y).left) (fun _ => -1)))
    (hg : ∀ y, (g y).IsGen)
    (w : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j))) (hw : w.IsGen) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a β')
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a 0 k)) (dε n j)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) J, Good D.P.L z J →
        val u (r ≫ eSec D.P.A) z J = val (g mu) r z J ^ n * val (g (h mu)) r z J ^ j * val D.rig r z J ^ (n + j) := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (g mu) (hg mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (g (h mu)) (hg _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rig D.rig_gen (n + j)
  have i₀ : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _
  have a₁ : ∀ χ, DVR.cP D (𝟙_ _) χ = D.c χ := fun χ => by rw [DVR.cP, i₀, Category.id_comp]
  have a₂ : η[D.P.A] = 1 := by rw [Hom.one_def, i₀, Category.id_comp]
  have z₃ : η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu) = D.c mu := by
    refine (MonObj.comp_mul _ (𝟙 _) (DVR.cP D _ mu)).trans ?_
    rw [DVR.comp_cP, Category.comp_id, a₂, _root_.one_mul, a₁]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (toUnit D.P.A).left (eSec D.P.A)
    (congrArg (fun q => q.left) (toUnit_unique (η[D.P.A] ≫ toUnit _) (𝟙 _))) (fun U _ f => by
      have q₁ := prod_t D a β' n j η[D.P.A] f
      have q₂ := prod_t D a 0 n j (η[D.P.A] ≫ padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)) f
      have b₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      conv_rhs at q₁ => rw [a₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, ← hh, cPoint_zero, _root_.mul_one]
      simp only [Over.comp_left, Category.assoc] at q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      have a₃ : eSec D.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left := congrArg (fun q => q.left) a₂
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) h₃)
  have hc := corr_of_val D.P.isLB (t := LB.pullGen D.P.L _ _ u (eSec D.P.A))
    (t' := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂) p₃) fun y J hJ => by
      rw [val_pull hJ, Category.id_comp]; exact vu y J hJ
  refine ⟨u, hu, fun Z r z J hJ => (val_pull hJ _ _ _).symm.trans ((val_corr hJ hc r).trans ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) (v₃ _ _ _ _))

theorem val_tau_zero (D : DegPre R) (hB : D.TauBimult) (x : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau x 0) (𝟙 _) z J = 1 := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv,
    congrArg (fun w => val (D.psi w) (𝟙 _) z J) (add_zero x), mul_inv_cancel, _root_.one_mul,
    GlobalTheory.PsiInPow.val_psi_zero D hB hJ, inv_inv, mul_inv_cancel]

def germK (K : Type) [Field K] (z : Sp K) : K →+* (Sp K).presheaf.stalk z :=
  ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem gs_sec {K : Type} [Field K] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) (z : Sp K) (c : K) :
    gs e z ⊤ (scal p c) = germK K z c := by
  refine (gs_pull e p z ⊤ trivial _).trans ?_
  rw [he, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_generic (z : Sp (FractionRing R)) (r : R) :
    gs (𝟙 _) z ⊤ (scal (jK R) r) = germK (FractionRing R) z (algebraMap R _ r) := by
  have nat := congrArg (fun g => g.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  rw [gs_eq _ z ⊤ trivial]
  exact congrArg ((Sp (FractionRing R)).presheaf.germ ⊤ z trivial).hom nat.symm

theorem const_eq {S : Type} [CommRing S] {u u₀ p t k k' G : Sˣ} {c r : S} {m : ℤ} (e₁ : u.val = c * u₀.val)
    (e₂ : u = p * t * k ^ m) (ht : t = 1) (hk : k = k') (e₃ : p.val = r * G.val) (e₄ : u₀ = G * k' ^ m) : c = r := by
  subst ht hk e₂
  refine (Units.mul_left_inj u₀).1 ?_
  rw [← e₁, e₄, _root_.mul_one, Units.val_mul, Units.val_mul, e₃, _root_.mul_assoc]

theorem exists_gen_fac : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (r : D.toPre.X → R) (g : ∀ y : D.toPre.X, LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => (D.toPre.c y).left) (fun _ => -1))), (∀ y, (g y).IsGen) → (∀ y (z : (TK R).left) (J), Good D.toPre.P.L z J → (val (D.toPre.psi y) (𝟙 _) z J ^ N * (val (D.toPre.psi (h y)) (𝟙 _) z J)⁻¹).val = gs (𝟙 _) z ⊤ (scal (jK R) (r y)) * (val (g y) (toUnit (TK R)).left z J ^ N * (val (g (h y)) (toUnit (TK R)).left z J)⁻¹).val) → ∀ ν : D.toPre.X, ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1))), u₀.IsGen ∧ ∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) (r ν))) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ hR D a a' h h' hE N _ r g hg hr ν
  have ha : IsMonHom a := hE.1
  have hh : ∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a := hE.2.2.2.1
  obtain ⟨w, hw⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hR D a a' h h' hE N (-1) ν 0 (shift h h' N (-1) ν) (zero_add _).symm
  obtain ⟨u₀, hu₀, v₀⟩ := exists_normalised D.toPre a h hh N (-1) ν _ g hg w hw
  refine ⟨u₀, hu₀, fun u hu => ?_⟩
  obtain ⟨c, hc⟩ := (fac_exists_unique_const R hR D a h ha hh N (-1) ν 0 _ u₀ hu₀).2.2 u hu.1
  suffices e : c = algebraMap R (FractionRing R) (r ν) by subst e; exact hc
  obtain ⟨z⟩ : Nonempty (Sp (FractionRing R)) := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  choose J hJ using fun ψ : Sp (FractionRing R) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  have j₁ : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : (DegPre.zF D.toPre (FractionRing R)).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (toUnit (TK R)).left ≫ eSec D.toPre.P.A := by
    refine (congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) (FractionRing R))) (toUnit _ ≫ η[D.toPre.P.A]))).trans ?_
    show (jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left) ≫ eSec D.toPre.P.A = _
    rw [j₁, Category.id_comp]
  have e₁ := hc _ (DegPre.zF D.toPre (FractionRing R)).left z J hJ
  have e₂ := hu.2 z J hJ
  have e₃ := hr ν z J hJ
  have e₄ := v₀ _ (toUnit (TK R)).left z J hJ
  have e₅ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (toUnit (TK R)).left z J :=
    (val_pull hJ _ _ _).trans (congrArg (fun q => val D.toPre.rig q z J) (Category.id_comp _))
  rw [j₁, zpow_natCast, zpow_neg_one] at e₂
  rw [zpow_natCast, zpow_neg_one] at e₄
  have e₆ := gs_sec _ _ (congrArg (fun q => q.left) z₁) z c
  have e₇ := gs_generic z (r ν)
  exact (germK (FractionRing R) z).injective (e₆.symm.trans ((const_eq e₁ e₂ (val_tau_zero D.toPre D.tau_bimult ν hJ) e₅ e₃
    ((congrArg (fun q => val u₀ q z J) z₂).trans e₄)).trans e₇))

end GlobalTheory.TwNorm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.trel_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  intro R _ _ _ hR D a a' h h' hE n j ν mu β₀ β₁ β₂ s₀ s₁ s₂ h₁ h₂ hν hνμ
  have hL := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hR D a a' h h' hE n j ν β₀ β₁ h₁
  obtain ⟨⟨u₁, hu₁⟩, -, -⟩ := GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 n j ν β₀ β₁ u₀ hu₀
  intro u hu Z x z J hJ
  have hc : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.trF D.toPre (FractionRing R) ν).left =
      (DegPre.trF D.toPre (FractionRing R) (ν + mu)).left := by
    rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, add_comm]
  have FE : FormEq (Sum.elim (dφ D.toPre a mu β₁ β₂) (fun k => (DegPre.trF D.toPre (FractionRing R) mu).left ≫ dφ D.toPre a ν β₀ β₁ k))
      (Sum.elim (dε n j) (dε n j)) (dφ D.toPre a (ν + mu) β₀ β₂) (dε n j) := by
    intro U _ g
    simp only [dφ, dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hc]
    simp only [zpow_neg, Finset.prod_inv_distrib, Category.assoc]
    group
  obtain ⟨w, hw, hwv⟩ := exists_gen hL FE _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ u _ hu.1
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ u₁ hu₁.1 _))
  have hwf : IsFac D.toPre a h n j (ν + mu) β₀ β₂ w := by
    refine ⟨hw, fun z' J' hJ' => ?_⟩
    rw [hwv _ _ z' J' hJ', val_mul hJ', val_pull hJ', hu.2 z' J' hJ', GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint R hR D a a' h h' hE n j ν mu β₀ β₁ h₁ u₁ hu₁ z' J' hJ']
    rw [mul_comm]
    exact inv_mul_cancel_right _ _
  have e1 := hν u₁ hu₁ Z (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J hJ
  have e2 := hνμ w hwf Z x z J hJ
  rw [hwv _ _ z J hJ, val_mul hJ, val_pull hJ, ← hc] at e2
  simp only [Category.assoc] at e1 e2 ⊢
  rw [e2, e1, Units.val_mul]
  ring
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  first | exact @GlobalTheory.TwFam.texp_pull | exact GlobalTheory.TwFam.texp_pull | (intros; apply GlobalTheory.TwFam.texp_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twisted_section_related_at_zero_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (s₀ : SecT D.toPre a N (-1) 0) (s' : SecT D.toPre a N (-1) (shift h h' N (-1) 0)), (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval s' x z J = sval s₀ x z J) → TRel h 0 s₀ s' := by
  first | exact @GlobalTheory.TwFac.trel_zero | exact GlobalTheory.TwFac.trel_zero | (intros; apply GlobalTheory.TwFac.trel_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  first | exact @GlobalTheory.TwFam.PullRel.main | exact GlobalTheory.TwFam.PullRel.main | (intros; apply GlobalTheory.TwFam.PullRel.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_pullbackTwistedSection_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  first | exact @GlobalTheory.TwFam.exists_isPullT | exact GlobalTheory.TwFam.exists_isPullT | (intros; apply GlobalTheory.TwFam.exists_isPullT <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.SumFE

open GlobalTheory.IndivisibleSection (smulSec)

theorem sval_smulSec {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (smulSec a s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem app_eq_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) (j) :
    (h.app _).hom (s.f j) = (h.app _).hom (s'.f j) := by
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ (𝟙 Y' ≫ h)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)

theorem sec_eq_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval s (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J = sval s' (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J) → s = s' := by
  intro R _ _ _ hB D K _ φ ε s s' H
  have := hB.1
  have := hB.2.2.2
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine DVR.SecOps.sec_ext fun j => sub_eq_zero.1 ?_
  refine (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R _ (IsAdicComplete.le_jacobson_bot (maximalIdeal R)) D.toPre.P.A).1 _
    (DVR.linComb_isLB _ D.toPre.P.isLB φ ε) ⟨fun i => s.f i - s'.f i, fun i j => by
      simp only [map_sub, s.compat, s'.compat, mul_sub]⟩ (fun e i => ?_) j
  exact (map_sub _ _ _).trans (sub_eq_zero.2 (app_eq_of_sval D.toPre.P.isLB (fun y J hJ => H e _ (𝟙 _) y J hJ) i))

theorem sec_eq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (K : Type) [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.P.L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J → sval s (x ≫ (DegPre.prB D (FractionRing R)).left) z J = sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J) → s = s' := by
  intro R _ _ D K _ φ ε s s' H
  have := D.P.isAb.smooth
  have : IsDominant (TF (R := R) (FractionRing R)).hom := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)) ∘
      PrimeSpectrum.comap (algebraMap (FractionRing R) (FractionRing R)))
    rw [Algebra.algebraMap_self, PrimeSpectrum.comap_id]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    have : IsAffine (TF (R := R) (FractionRing R)).left := inferInstanceAs (IsAffine (Spec _))
    quasiCompact_of_compactSpace _
  have := IsSchemeTheoreticallyDominant.of_isDominant (X := Spec (CommRingCat.of (FractionRing R)))
    (TF (R := R) (FractionRing R)).hom
  have : IsSchemeTheoreticallyDominant (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback _ D.P.A.hom)
  have : QuasiCompact (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) := inferInstance
  exact DVR.SecOps.sec_ext fun j => (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom).app_injective _
    (app_eq_of_sval D.P.isLB (fun y J hJ => H _ (𝟙 _) y J hJ) j)

theorem trF_prB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (mu : D.X), (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left := by
  intro R _ _ D mu
  rw [← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_snd, padd, padd, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc]

theorem gs_scal_generic {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Z : Scheme.{0}}
    (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R) :
    gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) =
      gs x z ⊤ (scal ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) r)) := by
  have e := congrArg (fun h => h.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have w : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom =
      ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
    refine (Over.w _).trans ((Over.w (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_)
    congr 1
    change Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) ≫ jK R = jK R
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine (gs_pull x _ z ⊤ trivial _).symm.trans (congrArg (gs x z ⊤) ?_)
  change scal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) r = _
  rw [w, scal, scal, e]
  rfl

theorem scal_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R), (r ≠ 0 → IsUnit (gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r))) ∧ ∀ (c : FractionRing R) (r' : R), c * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) r' → gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) * gs x z ⊤ (scal (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left c) = gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r') := by
  intro R _ _ D Z x z r
  refine ⟨fun hr => ?_, fun c r' hc => ?_⟩
  · have hu : IsUnit (algebraMap R (FractionRing R) r) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    rw [gs_scal_generic, gs_eq _ z ⊤ trivial]
    exact ((((hu.map _).map _).map _).map _)
  · rw [gs_scal_generic, gs_scal_generic, ← hc, ← gs_mul x z ⊤ trivial, mul_comm c]
    simp only [scal, map_mul]

theorem tfe_of_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  intro R _ _ _ hB D a a' h h' hE n j Ix w s F σ hs hF hw hrel mu β
  generalize hβ' : β + shift h h' n j mu = β'
  intro u hu
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hB D a a' h h' hE n j mu β β' hβ'.symm
  obtain ⟨c, hc⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hB D a h hE.1 hE.2.2.2.1 n j mu β β' u₀ hu₀).2.2 u hu.1
  obtain ⟨⟨r', r⟩, hrc⟩ := IsLocalization.surj (nonZeroDivisors R) c
  have hTw : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := Over.w _
  have hT := trF_prB R D.toPre mu
  generalize hTe : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left = T at hTw hT
  have mkG : ∀ t : SecT D.toPre a n j β, ∃ G : SecT D.toPre a n j β', ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left)
      (z : Z) (J), Good D.toPre.P.L z J → sval G y z J = sval t (y ≫ T) z J * (val u₀ y z J).val := by
    intro t
    obtain ⟨G, hG⟩ := exists_sec hL (φ' := tφ D.toPre a β') (ε' := tε n j) (fun U _ g => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, dε, zpow_neg, Finset.prod_inv_distrib, hTe]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec t T u₀ hu₀)
    exact ⟨G, fun Z y z J hJ => (hG Z y z J hJ).trans (sval_pullMulSec t T u₀ hu₀ y z hJ)⟩
  have key : ∀ (b b' : D.toPre.X) (t : SecT D.toPre a n j b) (t' : SecT D.toPre a n j b'), b = β → b' = β' →
      TRel h mu t t' → ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      gs y z ⊤ (scal D.toPre.P.A.hom r.1) * sval t' y z J =
        gs y z ⊤ (scal D.toPre.P.A.hom r') * (sval t (y ≫ T) z J * (val u₀ y z J).val) := by
    intro b b' t t' h1 h2 hR Z y z J hJ
    subst h1 h2
    obtain ⟨G, hG⟩ := mkG t
    have e : smulSec (scal D.toPre.P.A.hom r.1) t' = smulSec (scal D.toPre.P.A.hom r') G :=
      sec_eq_of_generic R D.toPre (Fin 5) _ _ _ _ fun Z x z J hJ => by
        rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hR u hu Z x z J hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT,
          ← (scal_generic R D.toPre Z x z r.1).2 c r' hrc, Category.assoc]
        ring
    rw [← hG _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, e]
  obtain ⟨G, hG⟩ := mkG (F β)
  have eB : smulSec (scal D.toPre.P.A.hom r.1) (F β') = smulSec (scal D.toPre.P.A.hom r') G := by
    refine sec_eq_of_thick R hB D (Fin 5) _ _ _ _ fun e Z x z J hJ => ?_
    rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ]
    obtain ⟨x', hx'⟩ : ∃ x' : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left,
        x' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ T :=
      ⟨pullback.lift _ (x ≫ pullback.snd _ _) (by
        rw [Category.assoc, hTw]
        exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)),
        pullback.lift_fst _ _ _⟩
    classical
    have hS : ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun i hi =>
      by_contra fun hc => hi ((hs e).mem_toFinset.2 hc)
    generalize (hs e).toFinset = S at hS
    have e₁ := hF e ((S ∪ S.image (σ mu).symm).image (σ mu)) (fun i hi => hS i fun m => hi (Finset.mem_image.2
      ⟨(σ mu).symm i, Finset.mem_union_right _ (Finset.mem_image_of_mem _ m), (σ mu).apply_symm_apply i⟩)) β' Z x z J hJ
    have e₂ := hF e (S ∪ S.image (σ mu).symm) (fun i hi => hS i fun m => hi (Finset.mem_union_left _ m)) β Z x' z J hJ
    rw [hx'] at e₂
    rw [e₁, e₂, Finset.sum_filter, Finset.sum_filter, Finset.sum_image (σ mu).injective.injOn, Finset.sum_mul,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : w i = β
    · have hi' : w (σ mu i) = β' := by rw [hw, hi, hβ']
      rw [if_pos hi, if_pos hi']
      exact key _ _ _ _ hi hi' (hrel mu i) _ _ z J hJ
    · have hi' : ¬ w (σ mu i) = β' := fun h2 => hi (add_right_cancel ((hw mu i).symm.trans (h2.trans hβ'.symm)))
      rw [if_neg hi, if_neg hi', zero_mul, mul_zero, mul_zero]
  intro Z x z J hJ
  obtain ⟨hunit, hmul⟩ := scal_generic R D.toPre Z x z r.1
  refine (hunit (nonZeroDivisors.ne_zero r.2)).mul_left_cancel ?_
  rw [← sval_smulSec _ _ _ _ hJ, eB, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT, ← hmul c r' hrc,
    Category.assoc]
  ring

end GlobalTheory.TwFam.SumFE
end
end
