module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle897
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.TwistSize.main | exact GlobalTheory.HilbFam.TwistSize.main | (intros; apply GlobalTheory.HilbFam.TwistSize.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.Axes

theorem injective_of_section {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q]
    [Module R Q] [Module.Finite R M] [Module.Projective R M] [Module.Finite R Q] [Module.Projective R Q]
    (N : M →ₗ[R] Q) (P : Q →ₗ[R] M) (hNP : N ∘ₗ P = LinearMap.id)
    (hr : ∀ p, Module.rankAtStalk (R := R) M p = Module.rankAtStalk (R := R) Q p) : Function.Injective N := by
  obtain ⟨e, -, -⟩ := ((LinearMap.exact_subtype_ker_map N).splitSurjectiveEquiv
    (LinearMap.ker N).injective_subtype ⟨P, hNP⟩)
  haveI : Module.Projective R (LinearMap.ker N × Q) := Module.Projective.of_equiv e
  haveI : Module.Projective R (LinearMap.ker N) :=
    Module.Projective.of_split (LinearMap.inl R _ Q) (LinearMap.fst R _ Q) (by ext x <;> simp)
  haveI : Module.Finite R (LinearMap.ker N) :=
    Module.Finite.of_surjective ((LinearMap.fst R _ Q) ∘ₗ e.toLinearMap)
      (fun x ↦ ⟨e.symm (x, 0), by simp⟩)
  have h1 := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod] at h1
  have h0 : Module.rankAtStalk (R := R) (LinearMap.ker N) = 0 := by
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hr p] at this
    simpa using this
  haveI := Module.rankAtStalk_eq_zero_iff_subsingleton.1 h0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker N) 0)

variable {R : Type} [CommRing R]

theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ₁ φ₂ : X' ⟶ X} (e : φ₁ = φ₂)
    (h₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (h₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) {a : HO1 s}
    {a' : HO1 s'} : IsPullO h₁ a a' ↔ IsPullO h₂ a a' := by
  subst e; rfl

theorem isPullO_id {X : Scheme.{0}} (s : X ⟶ Sp R) (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (a : HO1 s) :
    IsPullO h a a := by
  unfold IsPullO
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes (𝟙 X) s)
    { app := fun p ↦ (homOfLE (show p.unop.1.1 ≤ p.unop.1.2 from p.unop.2)).op
      naturality := fun _ _ _ ↦ Subsingleton.elim _ _ } ?_ a
  intro p b
  simp only [pairRes, pairPull, secPull, Sec.res, CoefMap.restrict]
  simp [Scheme.Hom.appLE, mp]
  rfl

abbrev pb {Y A : Over (Sp R)} (f : Y ⟶ A) : HO1 A.hom →ₗ[R] HO1 Y.hom := pullHO1 (overW f)

theorem pb_comp {Z Y A : Over (Sp R)} (f : Z ⟶ Y) (g : Y ⟶ A) (a : HO1 A.hom) :
    pb (f ≫ g) a = pb f (pb g a) := by
  have h'' : (f.left ≫ g.left) ≫ A.hom = Z.hom ≫ spMap (RingHom.id R) := by
    have e : (f ≫ g).left = f.left ≫ g.left := by simp
    rw [← e]; exact overW (f ≫ g)
  have k := (GlobalTheory.T.structureSheaf_pullback_relations_basic R A.left Y.left A.hom Y.hom g.left (overW g)).2.2 Z.left Z.hom f.left (overW f) h''
    a (pb g a) (pb f (pb g a)) (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact ((isPullO_congr (show f.left ≫ g.left = (f ≫ g).left by simp) h'' (overW (f ≫ g))).1 k).eq_pullHO1.symm

theorem pb_id (A : Over (Sp R)) (a : HO1 A.hom) : pb (𝟙 A) a = a := by
  have h : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  exact ((isPullO_congr (Over.id_left A).symm h (overW (𝟙 A))).1 (isPullO_id A.hom h a)).eq_pullHO1.symm

theorem pb_one (Y A : Over (Sp R)) [GrpObj A] (u : Y ⟶ 𝟙_ (Over (Sp R))) (a : HO1 A.hom) :
    pb (u ≫ η[A]) a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  rw [pb_comp, (GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ (pb η[A] a), map_zero]

theorem isPullO_zero_iff {Y A : Over (Sp R)} (f : Y ⟶ A) (c : HO1 A.hom) : IsPullO (overW f) c 0 ↔ pb f c = 0 :=
  ⟨fun e ↦ e.eq_pullHO1.symm, fun e ↦ e ▸ isPullO_pullHO1 _ c⟩

end Axes


open Axes in
theorem axesO1_of_cohomology_structure : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
    ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b,
      e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → AxesVanishingStructureSheafDegOne := by
  intro hS R _ A _ g hA hg c h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨f1, p1, r1⟩, -⟩ := hS R A g hA hg
  obtain ⟨⟨f2, p2, r2⟩, -⟩ := hS R (A ⊗ A) (g + g) hA2 hg2
  let N : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
    LinearMap.prod (pb (lift (𝟙 A) 1)) (pb (lift 1 (𝟙 A)))
  let P : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
    LinearMap.coprod (pb (fst A A)) (pb (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pb (lift (𝟙 A) 1) (pb (fst A A) x.1 + pb (snd A A) x.2) = x.1
      rw [map_add (f := _), ← pb_comp, ← pb_comp, lift_fst, lift_snd, pb_id]
      rw [show (1 : A ⟶ A) = toUnit A ≫ η[A] from rfl, pb_one, add_zero]
    · show pb (lift 1 (𝟙 A)) (pb (fst A A) x.1 + pb (snd A A) x.2) = x.2
      rw [map_add (f := _), ← pb_comp, ← pb_comp, lift_fst, lift_snd, pb_id]
      rw [show (1 : A ⟶ A) = toUnit A ≫ η[A] from rfl, pb_one, zero_add]
  have hinj := injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N c = N 0)
  rw [map_zero]
  exact Prod.ext ((isPullO_zero_iff _ c).1 h₁) ((isPullO_zero_iff _ c).1 h₂)

end GlobalTheory.Obs
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CyclotomicGlobalSections

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A)) :
    ∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  have hqk : (q : IsLocalRing.ResidueField A) ≠ 0 := by
    have := hq.map (IsLocalRing.residue A)
    simpa using this.ne_zero
  have hsepk : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).Separable :=
    (Polynomial.separable_X_pow_sub_C 1 hqk one_ne_zero).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ hdeg hsepk
  obtain ⟨b0, rfl⟩ := IsLocalRing.residue_surjective a0
  have hred : ∀ p : Polynomial A, IsLocalRing.residue A (p.eval b0) =
      (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A b0) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have h1 : (Polynomial.cyclotomic q A).eval b0 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hred, Polynomial.map_cyclotomic]
    all_goals exact ha0
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q A)).eval b0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hred, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]
    have := hsepk.aeval_derivative_ne_zero (x := IsLocalRing.residue A b0) (by simpa [Polynomial.aeval_def] using ha0)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q A)
    (Polynomial.cyclotomic.monic q A) b0 h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha

end GlobalTheory.EtC.CyclotomicGlobalSections


open GlobalTheory.EtC.ConnectedGlobalSections in
theorem GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  intro q _ A _ hA hq j
  obtain ⟨ζ0, hζ0⟩ := GlobalTheory.EtC.CyclotomicGlobalSections.exists_cyclotomic_root q A hA hq
  obtain ⟨hH, -⟩ := hA
  haveI := hH
  let e : Sec (tw q j) (Spec (CommRingCat.of A)) ≃+ Ht q (sp A) 0 j :=
    AddEquiv.ofBijective (AddMonoidHom.mk' (secClass (tw q j))
      (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q j) _).2.2.1)
      (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q j) _).2.1
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1 := fun x hx => by
    have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
    · exact Or.inr (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)).symm
    · exact Or.inl ((hu.mul_left_eq_zero).1 h0)
  let φ : ZMod q →+ Sec (tw q j) (Spec (CommRingCat.of A)) :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • twGen j ζ
      map_zero' := zero_smul _ _
      map_add' := fun c d => add_smul (ULift.up c : ULift.{1} (ZMod q)) (ULift.up d) (twGen j ζ) }
  have hφ : ∀ c : ZMod q, φ c = c.val • twGen j ζ := fun c => by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]; rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro c d h
      rw [hφ, hφ] at h
      exact scalar_eq ζ c d h
    · intro y
      obtain ⟨n, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidem) ζ y
      exact ⟨(n : ZMod q), by rw [hφ, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]⟩
  exact ⟨((AddEquiv.ofBijective φ hbij).trans e).symm⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_sh_acyclic_twists : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  intro q _ A _ hA _ T _ _ hfin s i hs
  obtain ⟨hH, hsep⟩ := hA
  obtain ⟨ι, hι, F, hF, hAF, e, hHF, hF'⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A T
  exact acycF_of_pi_sh (ZMod q) (tw q i) ι F T ⟨e.toRingEquiv⟩
    (fun j => ⟨hHF j, (hF' j).1⟩) s hs

end GlobalTheory.EtC.GmStep
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_unitClass : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  first
  | exact @GlobalTheory.EtC.red_one
  | exact GlobalTheory.EtC.red_one
  | (intros; apply GlobalTheory.EtC.red_one <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  first
  | exact @GlobalTheory.EtC.TwPairUniq.main
  | exact GlobalTheory.EtC.TwPairUniq.main
  | (intros; apply GlobalTheory.EtC.TwPairUniq.main <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.class_zero_of_geometric_points : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ) (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  first | (exact @GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (exact GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (intros; apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.h_zero_pullback_twist_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'), IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' → (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.h_zero_pull_bijective) | (exact GlobalTheory.EtC.h_zero_pull_bijective) | (intros; apply GlobalTheory.EtC.h_zero_pull_bijective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.restrictScalars_resolution_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧ ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  first
  | exact @GlobalTheory.EtC.restrRes_comparison
  | exact GlobalTheory.EtC.restrRes_comparison
  | (intros; apply GlobalTheory.EtC.restrRes_comparison <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R) (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) → ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  first
  | exact @GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | exact GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | (intros; apply GlobalTheory.EtC.semiMap_op_eq_zero_of_kill <;> assumption)
end

section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_le_map_fil : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C]
    (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f →
    ∀ N, fil δ' N ≤ (fil δ N).map f := by
  intro B _ J δ C _ J' δ' f hf hJ N
  subst hJ
  have hmul : ∀ {m n : ℕ} {a b : C}, a ∈ (fil δ m).map f → b ∈ (fil δ n).map f →
      a * b ∈ (fil δ (m + n)).map f := by
    intro m n a b ha hb
    have : (fil δ m).map f * (fil δ n).map f ≤ (fil δ (m + n)).map f := by
      rw [← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_le.2 fun x hx y hy ↦ ExpBij.mul_mem_dpFil δ hx hy)
    exact this (Ideal.mul_mem_mul ha hb)
  have hzero : ∀ c : C, c ∈ (fil δ 0).map f := by
    intro c
    rw [fil_zero_eq_top, Ideal.map_top]
    trivial
  have hdp : ∀ y ∈ J.map f, ∀ n, δ'.dpow n y ∈ (fil δ n).map f := by
    intro y hy
    change y ∈ Ideal.span (f '' (J : Set B)) at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro n
      rw [hf.dpow_comp a ha]
      exact Ideal.mem_map_of_mem _ (ExpBij.dpow_mem_dpFil δ ha n)
    | zero =>
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hzero _
      · rw [δ'.dpow_eval_zero hn.ne']
        exact Ideal.zero_mem _
    | add x y hx hy ihx ihy =>
      intro n
      rw [δ'.dpow_add hx hy]
      refine Ideal.sum_mem _ fun k hk ↦ ?_
      have hk' : k.1 + k.2 = n := by simpa using hk
      rw [← hk']
      exact hmul (ihx k.1) (ihy k.2)
    | smul c x hx ih =>
      intro n
      rw [smul_eq_mul, δ'.dpow_mul hx]
      exact Ideal.mul_mem_left _ _ (ih n)
  have hprod : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J.map f) →
      (l.map fun p ↦ δ'.dpow p.1 p.2).prod ∈ (fil δ (l.map Prod.fst).sum).map f := by
    intro l hl
    induction l with
    | nil => exact hzero _
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact hmul (hdp p.2 (hl p (by simp)) p.1) (ih fun q hq ↦ hl q (by simp [hq]))
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, h1, h2, rfl⟩
  exact Ideal.map_mono (ExpBij.dpFil_anti δ h2) (hprod l h1)

end GlobalTheory.PDA
end

section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_isSubDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (N : ℕ), 1 ≤ N →
    δ.IsSubDPIdeal (fil δ N) := by
  intro B _ J δ N hN
  refine ⟨GlobalTheory.Cris.ExpBij.dpFil_le δ hN, fun n hn j hj ↦ ?_⟩
  have h := GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hN hj n
  exact GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hn)) h

end GlobalTheory.PDA
end
