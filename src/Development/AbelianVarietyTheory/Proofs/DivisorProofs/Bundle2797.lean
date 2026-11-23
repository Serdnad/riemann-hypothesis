module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle432
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle002
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle180
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DefectHom

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zero (D : DegPre R) : D.c 0 = 1 := by
  have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem c_neg (D : DegPre R) (a : D.X) : D.c (-a) = (D.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : D.c (-a + a) = D.c (-a) * D.c a := D.c_add _ _
  rw [neg_add_cancel, c_zero] at h
  exact h.symm

theorem pt_neg (D : DegPre R) (a : D.X) : toUnit (TK R) ≫ D.c (-a) = (toUnit (TK R) ≫ D.c a)⁻¹ := by
  rw [c_neg, GrpObj.comp_inv]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem neg_pt_left (D : DegPre R) (a : D.X) : ptK (D.c (-a)) = D.xK a ≫ (ι[D.P.A]).left := by
  show (toUnit (TK R) ≫ D.c (-a)).left = _
  rw [pt_neg, Hom.inv_def, Over.comp_left]

theorem exists_defect (D : DegPre R) (χ : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val (D.psi χ) (𝟙 _) z J := by
  let t := LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
  have hf : FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (-χ))) (fun k => D.xK χ ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] k))
      (Sum.elim (fun _ => -1) ![1, -1]) (fun _ : PUnit => ptK (D.c χ)) (fun _ => -1) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, neg_pt_left]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
    simp only [zpow_neg, zpow_one]
    group
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht (D.psi χ) (D.psi_gen χ) hf
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [Category.id_comp]
  rw [← e₁]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem exists_evenDefect_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R),
    D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  intro R _ _ _ D hB
  choose h hh using exists_defect D
  refine ⟨h, fun a b => ?_, hh⟩
  let z : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  refine gm_unitOn_inj z ?_
  have g1 := GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio R D (TK R) (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) z J hJ
  have g2 := GlobalTheory.T.tau_period_val_neg_cubical_ratio R D hB a b z J hJ
  rw [← pt_neg, ← pt_neg, ← pt_add] at g1
  rw [val_tau D a b hJ, val_tau D (-a) (-b) hJ, ← neg_add] at g2
  have e₀ := hh (a + b) z J hJ
  have e₁ := hh a z J hJ
  have e₂ := hh b z J hJ
  change val D.sym (D.xK (a + b)) z J * _ = val D.sym (D.xK a) z J * val D.sym (D.xK b) z J * _ at g1
  rw [show unitOn (h a * h b) = unitOn (h a) * unitOn (h b) from map_mul _ _ _, map_mul]
  generalize val D.sym (D.xK (a + b)) z J = s₀ at g1 e₀
  generalize val D.sym (D.xK a) z J = s₁ at g1 e₁
  generalize val D.sym (D.xK b) z J = s₂ at g1 e₂
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h (a + b))) = k₀ at e₀ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h a)) = k₁ at e₁ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h b)) = k₂ at e₂ ⊢
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀; have a₁ := E e₁; have a₂ := E e₂; have b₁ := E g1; have b₂ := E g2
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) -a₀ + a₁ + a₂ + b₁ - b₂
end GlobalTheory.DefectHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreDense

theorem isPrime_map_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] : (I.map φ).IsPrime := by
  let _ := φ.toAlgebra
  have : Module.Flat A R := hf
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : I.map (algebraMap A R) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans ((Ideal.map_mono hI).trans hm.le)))
  have : Nontrivial (R ⧸ I.map (algebraMap A R)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I.map (algebraMap A R)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  have hmap : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) = maximalIdeal _ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R))) Ideal.Quotient.mk_surjective,
      ← hm, Ideal.map_map, Ideal.map_map]
    rfl
  have : IsLocalHom (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    ((local_hom_tfae _).out 1 3).2 hmap.le
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap
  have : IsDomain (R ⧸ I.map (algebraMap A R)) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

theorem exists_toStalk (o : Type) [CommRing o] (x : Sp o) : ∃ τ : CommRingCat.of o ⟶ (Sp o).presheaf.stalk x,
    (Sp o).fromSpecStalk x = Spec.map τ ∧ x.asIdeal.map τ.hom = maximalIdeal ((Sp o).presheaf.stalk x) := by
  have := x.isPrime
  let _ : Algebra o ((Spec (CommRingCat.of o)).presheaf.stalk x) := (StructureSheaf.toStalk o x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of o)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk o x
  exact ⟨StructureSheaf.toStalk o x, Spec.fromSpecStalk_eq' (CommRingCat.of o) x,
    IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (CommRingCat.of o)).presheaf.stalk x)⟩

theorem isPrime_fibre {o : Type} [CommRing o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Smooth s] {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hb : ξ ≫ s = spMap b)
    (he : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) : (((maximalIdeal R).comap b).map b).IsPrime := by
  have hreg := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal _ _ s (ξ (closedPoint R))
  have hp := isPrime_map_of_flat _ he.1 he.2.1
    ((maximalIdeal ((Sp o).presheaf.stalk (s (ξ (closedPoint R))))).map (s.stalkMap (ξ (closedPoint R))).hom)
  obtain ⟨τ, hτ, hmax⟩ := exists_toStalk o (s (ξ (closedPoint R)))
  have hc : τ ≫ s.stalkMap (ξ (closedPoint R)) ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    refine Eq.trans ?_ hb
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hτ, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    exact congrArg (· ≫ s) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ)
  have hx : (s (ξ (closedPoint R))).asIdeal = (maximalIdeal R).comap b :=
    congrArg (fun f : Sp R ⟶ Sp o => (f (closedPoint R)).asIdeal) hb
  have hb' : (Scheme.stalkClosedPointTo ξ).hom.comp ((s.stalkMap (ξ (closedPoint R))).hom.comp τ.hom) = b :=
    congrArg (fun q => q.hom) hc
  rwa [← hmax, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hb', hx] at hp

theorem mem_closure_fibre : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  intro o _ ζ g n F S s j _ φ BD d x _ _ h
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨-, -, hb, rfl, he, -⟩, ⟨ht, -, hj⟩, -⟩ := h
  have hq := isPrime_fibre s b ξ hb he
  let q : Sp R := (⟨((maximalIdeal R).comap b).map b, hq⟩ : PrimeSpectrum R)
  have hs : ∀ p : Sp R, s (ξ p) = spMap b p := fun p => congrArg (fun f : Sp R ⟶ Sp o => f p) hb
  have h₁ : ξ q ∈ Set.range j := by
    refine (hj q).2 fun hmem => ?_
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hq)).1 hmem
    have := ht.2 (Pi.single i 1) (Ideal.mem_sup_right (by simpa [Pi.single_apply] using hi)) i
    simp at this
  have h₂ : s (ξ q) = s (ξ (closedPoint R)) := by
    refine (hs q).trans (Eq.trans (PrimeSpectrum.ext (le_antisymm ?_ ?_)) (hs (closedPoint R)).symm)
    · exact Ideal.comap_mono (f := b) (Ideal.map_comap_le (f := b) (K := maximalIdeal R))
    · exact Ideal.le_comap_map (f := b) (I := (maximalIdeal R).comap b)
  have h₃ : ξ q ⤳ ξ (closedPoint R) := (specializes_closedPoint (R := R) q).map ξ.continuous
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_inter h₁ h₂)) (specializes_iff_mem_closure.1 h₃)

end GlobalTheory.FibreDense
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCoc

theorem alg {X U : Type} [AddCommGroup X] [CommGroup U] (F t P : X → X → U) (C : X → X → X → U) (ψ : X → U) (r : U)
    (hF : ∀ a b, P a b * F a b = t a b) (hP : ∀ a b, P a b = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹)
    (ht : ∀ a b, t a b = t b a) (hadd : ∀ a a' b, t (a + a') b * C a a' b = t a b * t a' b)
    (hC : ∀ a b c, C a b c = C b c a) :
    (∀ a b, F a b = F b a) ∧ ∀ a b c, F (a + b) c * F a b = F a (b + c) * F b c := by
  constructor
  · intro a b
    have comm : ψ (b + a) = ψ (a + b) := by rw [add_comm]
    have e₁ := congrArg Additive.ofMul (hF a b)
    have e₂ := congrArg Additive.ofMul (hF b a)
    have e₃ := congrArg Additive.ofMul (ht a b)
    have e₄ := congrArg Additive.ofMul (hP a b)
    have e₅ := congrArg Additive.ofMul (hP b a)
    have e₆ := congrArg Additive.ofMul comm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ e₆ ⊢
    linear_combination (norm := abel) e₁ - e₂ + e₃ - e₄ + e₅ + e₆
  · intro a b c
    have p₁ := hP (a + b) c
    rw [add_assoc] at p₁
    have e₁ := congrArg Additive.ofMul (hadd a b c)
    have e₂ := congrArg Additive.ofMul (hadd b c a)
    have s₁ := congrArg Additive.ofMul (ht a (b + c))
    have s₂ := congrArg Additive.ofMul (ht a b)
    have s₃ := congrArg Additive.ofMul (ht a c)
    have c₁ := congrArg Additive.ofMul (hC a b c)
    have f₁ := congrArg Additive.ofMul (hF (a + b) c)
    have f₂ := congrArg Additive.ofMul (hF a b)
    have f₃ := congrArg Additive.ofMul (hF a (b + c))
    have f₄ := congrArg Additive.ofMul (hF b c)
    have q₁ := congrArg Additive.ofMul p₁
    have q₂ := congrArg Additive.ofMul (hP a b)
    have q₃ := congrArg Additive.ofMul (hP a (b + c))
    have q₄ := congrArg Additive.ofMul (hP b c)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ s₁ s₂ s₃ c₁ f₁ f₂ f₃ f₄ q₁ q₂ q₃ q₄ ⊢
    linear_combination (norm := abel) e₁ - s₁ - e₂ + s₂ + s₃ - c₁ + f₁ + f₂ - f₃ - f₄ - q₁ - q₂ + q₃ + q₄

theorem exists_genPtMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

end GlobalTheory.PolDeg.SymCoc

namespace GlobalTheory.PolDeg


open GlobalTheory.PolDeg.SymCoc in
theorem half_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  intro R _ _ R' _ _ Q ρ D e f hρ hH
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₀, h₄, h₅⟩ := hH
  obtain ⟨κ, hκ⟩ : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := exists_genPtMap ρ hρ
  let z : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  let x : D.X → (TK R' ⟶ D.P.A) := fun a => toUnit (TK R') ≫ D.c a
  have hx : ∀ a a', x (a + a') = x a * x a' := fun a a' => by
    show toUnit (TK R') ≫ D.c (a + a') = _
    rw [D.c_add]
    exact MonObj.comp_mul _ _ _
  let ψ : D.X → ((TK R').left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J'
  let r : ((TK R').left.presheaf.stalk z)ˣ := val D.rigK (𝟙 _) z J'
  have hP : ∀ a b, val (D.tau a b) (𝟙 _) z J' = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hJ', val_mul hJ', val_mul hJ', val_inv, val_inv, val_inv]
  let laws := fun a a' b => GlobalTheory.LamRigid.lam_iso_laws (Sp R) (Sp R') Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub
    (spMap ρ) β β₂ w h₁ D.P.isAb h₂ h₃ h₀ (TK R') (x a) (x a') (x b) z J J' hJ hJ'
  let κo : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  let X : D.X → (TK R ⟶ Q.B) := fun a => toUnit (TK R) ≫ Q.c (e a)
  let y : D.X → (Over.mk ((TK R').hom ≫ spMap ρ) ⟶ Q.B) := fun a => κo ≫ X a
  have hy : ∀ a, (y a).left = (x a).left ≫ β := fun a => by
    simp only [y, X, x, κo, Over.comp_left, Over.homMk_left, Rosenlicht.toUnit_left, Over.mk_hom, Category.assoc]
    rw [h₄ a, ← Category.assoc κ, hκ, Category.assoc]
  have hq : ∀ a a' b, val (Q.tau (e (a + a')) (e b)) κ z J *
      @id ((TK R').left.presheaf.stalk z)ˣ (cubV Q.cub (T := Over.mk ((TK R').hom ≫ spMap ρ)) z J (y a) (y a') (y b)) =
      val (Q.tau (e a) (e b)) κ z J * val (Q.tau (e a') (e b)) κ z J := by
    intro a a' b
    have hc : LB.Gen.Corr Q.M.L _ _ _ _
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e a) (e b)) (Q.tau (e a') (e b))) :=
      corr_of_val Q.M.isLB fun y' J₀ hJ₀ => by
        have t₁ := Q.tau_add (e a) (e a') (e b) y' J₀ hJ₀
        rw [← map_add e a a'] at t₁
        refine (val_mul hJ₀ _ _ _).trans (Eq.trans ?_ (t₁.trans (val_mul hJ₀ _ _ _).symm))
        exact congrArg _ ((val_pull hJ₀ _ _ _).trans
          (congrArg (fun p => val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t p y' J₀) (Category.id_comp _)))
    calc _ = val (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left)) κ z J := by
          refine Eq.trans ?_ (val_mul hJ _ _ _).symm
          exact congrArg _ (val_cub Q.cub κo hJ (X a) (X a') (X b)).symm
      _ = _ := val_corr hJ hc κ
      _ = _ := val_mul hJ _ _ _
  have hqs : ∀ a b, val (Q.tau (e a) (e b)) κ z J = val (Q.tau (e b) (e a)) κ z J := fun a b =>
    val_corr hJ (corr_of_val Q.M.isLB fun y' J₀ hJ₀ => Q.tau_symm (e a) (e b) y' J₀ hJ₀) κ
  have hcub := isCub_cubV D.cub hJ'
  obtain ⟨hs, hc⟩ := alg (fun a b => gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)))
    (fun a b => lamVal w (lift (x a) (x b)).left z J J' * val (Q.tau (e a) (e b)) κ z J)
    (fun a b => val (D.tau a b) (𝟙 _) z J') (fun a a' b => cubV D.cub z J' (x a) (x a') (x b)) ψ r
    (fun a b => h₅ κ hκ a b z J J' hJ hJ') hP
    (fun a b => by
      beta_reduce
      rw [(laws a a b).1, hqs a b])
    (fun a a' b => by
      have e₁ := (laws a a' b).2 (y a) (y a') (y b) (hy a) (hy a') (hy b)
      rw [← hx] at e₁
      have e₂ := hq a a' b
      beta_reduce
      apply Additive.ofMul.injective
      have e₁' := congrArg Additive.ofMul e₁
      have e₂' := congrArg Additive.ofMul e₂
      simp only [ofMul_mul, id] at e₁' e₂' ⊢
      linear_combination (norm := abel) e₁' + e₂')
    (fun a b c => (hcub.s01 _ _ _).trans (hcub.s12 _ _ _))
  have inj : ∀ u v : (FractionRing R')ˣ, gm (𝟙 (TK R').left) z ⊤ (unitOn u) = gm (𝟙 (TK R').left) z ⊤ (unitOn v) →
      u = v := fun u v h =>
    ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (GlobalTheory.ArcData.unit_ext_field (𝟙 (Sp (FractionRing R'))) z fun _ => h)
  have hm : ∀ u v : (FractionRing R')ˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v =>
    map_mul (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))).inv.hom.toMonoidHom) u v
  refine ⟨fun a b => inj _ _ (hs a b), fun a b c => inj _ _ ?_⟩
  rw [hm, hm, map_mul, map_mul]
  exact hc a b c

end GlobalTheory.PolDeg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem mem_of_finite_conj {K : Type} [Field K] [IsAlgClosed K] (k₀ : Subfield K) (hk : IsAlgClosed k₀)
    (a : K) (h : Set.Finite {b : K | ∃ σ : K ≃+* K, (∀ c ∈ k₀, σ c = c) ∧ b = σ a}) : a ∈ k₀ := by
  haveI := hk
  by_contra ha
  have htr : Transcendental k₀ a := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k₀ a hdeg
    exact ha (hc ▸ c.2)
  have hc : ∀ c : k₀, ∃ σ : K ≃ₐ[k₀] K, σ a = a + algebraMap k₀ K c := by
    intro c
    have htr' : Transcendental k₀ (a + algebraMap k₀ K c) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub (isIntegral_algebraMap (x := c))).isAlgebraic)
    exact GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental htr htr'
  refine Set.infinite_of_injective_forall_mem (f := fun c : k₀ => a + algebraMap k₀ K c) ?_ ?_ h
  · intro c d hcd
    simpa using hcd
  · intro c
    obtain ⟨σ, hσ⟩ := hc c
    exact ⟨σ.toRingEquiv, fun b hb => σ.commutes ⟨b, hb⟩, hσ.symm⟩

theorem defOver_of_finite_orbit : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (Y : Scheme.{0}) (P : Sp K ⟶ Y),
    Set.Finite {P' : Sp K ⟶ Y | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ P' = spMap σ.toRingHom ≫ P} →
    DefOver k₀ P := by
  intro K _ _ k₀ hk Y P hfin
  classical
  let e := SpecToEquivOfLocalRing Y (CommRingCat.of K)
  let x := (e P).1
  let f := (e P).2.1
  have hP : P = Spec.map f ≫ Y.fromSpecStalk x := (e.left_inv P).symm
  let Φ : {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} → (Sp K ⟶ Y) :=
    fun g => e.symm ⟨x, g⟩
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    have := e.symm.injective h
    exact eq_of_heq (Sigma.mk.inj this).2
  have hloc : ∀ σ : K ≃+* K, IsLocalHom (f ≫ CommRingCat.ofHom σ.toRingHom).hom := by
    intro σ
    have : IsLocalHom f.hom := (e P).2.2
    show IsLocalHom (σ.toRingHom.comp f.hom)
    infer_instance
  let T : Set {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} :=
    {g | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ g.1 = f ≫ CommRingCat.ofHom σ.toRingHom}
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (hfin.subset ?_) hΦ.injOn
    rintro _ ⟨g, ⟨σ, hσ, hg⟩, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show Spec.map g.1 ≫ Y.fromSpecStalk x = _
    rw [hg, Spec.map_comp, Category.assoc, ← hP]
  have hmem : ∀ s, f.hom s ∈ k₀ := by
    intro s
    refine mem_of_finite_conj k₀ hk _ ((hT.image fun g => g.1.hom s).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨f ≫ CommRingCat.ofHom σ.toRingHom, hloc σ⟩, ⟨σ, hσ, rfl⟩, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (f.hom.codRestrict k₀ hmem)) ≫ Y.fromSpecStalk x, ?_⟩
  refine Eq.trans ?_ hP.symm
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem has_of_subsingleton : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ D : DegData R (maximalIdeal R), Subsingleton D.toPre.X → Has D := by
  intro R _ _ _ hR D hX
  haveI : IsNoetherianRing R := hR.1
  let A : PolAV (Spec (CommRingCat.of (FractionRing R))) := GlobalTheory.AmpleSpecialisation.baseChange D.toPre.P (jK R)
  let eA : (Over.pullback (jK R)).obj D.toPre.P.A ≅ A.A := by
    with_unfolding_all exact Iso.refl _
  have hA : IsMonHom eA.hom := by
    refine ⟨?_, ?_⟩
    · exact Category.comp_id _
    · show μ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      rfl
  have hw : ∃ w : LB.Iso (A.L.pull eA.hom.left) (D.toPre.P.L.pull (pullback.fst D.toPre.P.A.hom (jK R))), w.IsGen := by
    obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.toPre.P.isLB (pullback.fst D.toPre.P.A.hom (jK R)))
    exact ⟨GlobalTheory.PtTie.isoFromPullId w, GlobalTheory.PtTie.isoFromPullId_isGen hw⟩
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact ⟨D.toPre.P.A, inferInstance, inferInstance, A, GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb,
    ⟨⟨GlobalTheory.SelfUnif.selfPre D A eA hA hw, fun k _ =>
      GlobalTheory.SelfUnif.expBij D A eA hA hw GlobalTheory.globalFns_holds hI k⟩⟩⟩

end GlobalTheory.Mum
end
end
