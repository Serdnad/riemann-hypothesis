module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle031
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

theorem siegPre_lev_nsmul {S : Scheme.{0}} {h M : ℕ} {Bs : Type} [CommRing Bs] {ζ : Bs} {s : S ⟶ Sp Bs}
    (c : SiegPre h M ζ s) (n : ℕ) (b : Fin h ⊕ Fin h → ℤ) : c.lev (n • b) = c.lev b ^ n := by
  have h0 : c.lev 0 = 1 := by
    have := c.lev_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, c.lev_add, ih, pow_succ]

theorem geom_levZ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → (∀ a, (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = 1 ↔ ∃ b, a = M • b)) ∧ (∀ g : Over.mk x ⟶ (GlobalTheory.ZarhinFam.Zob c.A B), g ^ M = 1 → ∃ a, toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = g) ∧ ∀ a b, Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a) (toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro h M d S t c B _ _ Q la mu hZ hh hM hMo hd hcop hdu hker κ hκ k _ _ x β z hx hz
  have hla : IsMonHom la := hZ.2.2.2.1
  have hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hml : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  set X : Over.mk x ⟶ 𝟙_ (Over S) := toUnit (Over.mk x) with hXdef
  have hpt : ∀ a, X ≫ levZ c.lev (incZ c.A B) (actZ c.A B d la mu) (oMat d) κ a =
      mkZ c.A B (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a)) (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
    intro a
    rw [GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint c.A B d h (8 * h) la mu c.lev κ a]
    exact (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B X _ _ 1 1).1
  have geo := c.geom k x β z hx hz
  have geo1 : ∀ q, X ≫ c.lev q = 1 ↔ ∃ b, q = M • b := geo.1
  have htA := GlobalTheory.T.isogeny_bijective_on_torsion_coprime_degree c.A B la mu d M (Over.mk x) hla hmu hlm hml hcop
  have hK := GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod h M d κ (by omega) hκ
  have htor : ∀ q, (X ≫ c.lev q) ^ M = 1 := fun q => by rw [← comp_pow, c.lev_tors, comp_one]
  have hlev1 : ∀ q, (X ≫ c.lev q ≫ la = 1 ↔ X ≫ c.lev q = 1) := fun q => by
    constructor
    · intro e
      exact htA.1 _ (htor q) (by rw [Category.assoc]; exact e)
    · intro e
      rw [← Category.assoc, e, one_comp]
  have hlevM : ∀ q b, c.lev (q + M • b) = c.lev q := fun q b => by
    rw [c.lev_add, siegPre_lev_nsmul, c.lev_tors, _root_.mul_one]
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  ·
    rw [hpt a, (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a))
      (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) 1 1).2.2.1, ← (hK.1 a)]
    simp only [hlev1, geo1]
    exact (Fin.forall_fin_add (m := 4) (n := 4) (fun k : Fin 8 => ∃ b, κ k a = M • b)).symm
  ·
    obtain ⟨-, hpow, hone, hg'⟩ := GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => g ≫ pa c.A B i) (fun j => g ≫ pb c.A B j) g M
    have hgM : mkZ c.A B (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) = 1 := by
      rw [← hpow, ← hg', hg]
    obtain ⟨hu, hv⟩ := (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) g M).2.2.1.1 hgM
    have eu : ∀ i, ∃ q, X ≫ c.lev q = g ≫ pa c.A B i := fun i => geo.2.1 _ (hu i)
    have ev : ∀ j, ∃ q, X ≫ c.lev q ≫ la = g ≫ pb c.A B j := fun j => by
      obtain ⟨y, hyM, hy⟩ := htA.2 _ (hv j)
      obtain ⟨q, hq⟩ := geo.2.1 y hyM
      exact ⟨q, by rw [← Category.assoc, hq, hy]⟩
    choose qa hqa using eu
    choose qb hqb using ev
    let cc : Fin 8 → (Fin h ⊕ Fin h → ℤ) := fun k =>
      Fin.addCases (m := 4) (n := 4) (motive := fun _ => Fin h ⊕ Fin h → ℤ) qa qb k
    obtain ⟨a, ha⟩ := hK.2 cc
    refine ⟨a, ?_⟩
    rw [hpt a, hg']
    congr 1
    · funext i
      obtain ⟨b, hb⟩ := ha (Fin.castAdd 4 i)
      rw [hb, hlevM]
      exact (congrArg (X ≫ c.lev ·) (Fin.addCases_left (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) i)).trans (hqa i)
    · funext j
      obtain ⟨b, hb⟩ := ha (Fin.natAdd 4 j)
      rw [hb, hlevM]
      exact (congrArg (fun q => X ≫ c.lev q ≫ la) (Fin.addCases_right (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) j)).trans (hqb j)
  ·
    rw [hpt a, hpt b]
    have W := GlobalTheory.T.weilPairing_diagonal_zarhinBundle_eq_zeta_pow h M d S t c B Q la mu hZ hh hM hMo hd hcop hdu hker k x β z hx hz
      (fun k => κ k a) (fun k => κ k b)
    have hzM : z ^ M = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self (by omega : M ≠ 0), map_one, Units.val_one]
    obtain ⟨m, hm⟩ := (hκ.1 a b).symm.dvd
    have e : z ^ (2 * formZ d h (fun k => κ k a) (fun k => κ k b)) = z ^ (2 * omegaStd a b) := by
      have : 2 * formZ d h (fun k => κ k a) (fun k => κ k b) = 2 * omegaStd a b + (M : ℤ) * (2 * m) := by
        linear_combination 2 * hm
      rw [this, zpow_add, zpow_mul z (M : ℤ), zpow_natCast, hzM, one_zpow, _root_.mul_one]
    rw [e] at W
    exact W

end GlobalTheory.ZarhinFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UNormDown

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal
    (by rw [hπ]; exact hAc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π := by
    intro χ hχ
    have e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π) := by
      simp only [Category.assoc]
    have e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i := by
      rw [jK_spMap f fK hfK, Category.assoc, hgen]
    rw [e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]
    simp only [Category.assoc]
  have hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a} := by
    intro χ hχ
    obtain ⟨tK, h1, h2⟩ := T₂.gen
    exact hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev
      T₂.mono
  obtain ⟨a₀, ha₀, h₀⟩ := hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord (ψ j) (hψ j)
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  have idlAlong_eq_map_local {X : Scheme.{0}} (I : X.IdealSheafData) {R : Type}
      [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X) (U : X.affineOpens)
      (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
      idlAlong I χ = (I.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
    have hx : χ (closedPoint R) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map I U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have idlAlong_comp_local {X : Scheme.{0}} (I : X.IdealSheafData) {R S : Type}
      [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
      (χ : Sp R ⟶ X) (g : R →+* S) : idlAlong I (spMap g ≫ χ) = (idlAlong I χ).map g := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
    have hle' : ⊤ ≤ (spMap g ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap g x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [idlAlong_eq_map_local I χ ⟨U, hU⟩ hle, idlAlong_eq_map_local I _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (spMap g ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap g).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  apply GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← idlAlong_comp_local, hcomp, Category.assoc, h₀, hmp]
  simp only [← idlAlong_comp_local, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.UPoinc.UNormDown
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabTorsTrait

open GlobalTheory.ArcPull GlobalTheory.Mum.Recog

theorem labTors_of_oneTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  intro R _ _ _ hR D A lab hT k hk
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, iφ, _, hG, ha, c, H⟩ := hT
  have := hR.2
  have : CharZero W := (RingHom.charZero_iff iφ).1 inferInstance
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB' := D'.tau_bimult
  have c' : Compat φ (Kb W) := c
  obtain ⟨f', hf'⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws W (maximalIdeal W) bW D' A' G' hG U' (Kb W) k hk
  obtain ⟨ε, hε, iε, oε, wε⟩ := exists_ptHom ha c' em
  have e : ∀ p, f' (tr hD c' em hB' p) = ε (lab k p) := fun p => by
    obtain ⟨p₁, h₁, h₂, h₃⟩ := (lies_iff hD c' em hB' p (tr hD c' em hB' p)).2 rfl
    exact ((hf'.1 _ _).1 (H k hk p p₁ _ _ h₁ h₂ h₃ ((hε _ _).1 rfl))).symm
  have pw : ∀ x : TFK (R := R) (Kb R) ⟶ A.A, ε x ^ k = 1 ↔ x ^ k = 1 := fun x => by
    rw [← map_pow, ← map_one ε, iε.eq_iff]
  have hp : ∀ p, lab k p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← pw, ← e]
    exact (((hf'.1 _ _).2 rfl) w hw).1
  refine ⟨fun y hy => ?_, hp, fun p q => ?_, fun p q r h => ?_, fun p q z => ?_⟩
  · obtain ⟨p', hp'⟩ := hf'.2.1 (ε y) ((pw y).2 hy)
    obtain ⟨p, rfl⟩ := (tr_bij hD c' em hB' hk).2 p'
    exact ⟨p, iε (by rw [← e, hp'])⟩
  · rw [← iε.eq_iff, ← e, ← e, hf'.2.2.1, tr_equiv]
  · apply iε
    rw [map_mul, ← e, ← e, ← e]
    exact hf'.2.2.2.1 _ _ _ ((tr_add hD c' em hB' p q r).2 h)
  · rw [← tr_weil hD c' em hB' hk p q z, wε k _ _ (hp p) (hp q) z, ← e, ← e]
    exact hf'.2.2.2.2 _ _ (Units.map em.toRingHom.toMonoidHom z)

end GlobalTheory.Mum.LabTorsTrait
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8



theorem exists_cp_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  intro hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  let P₁ : GlobalTheory.UU.CP G₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W
  refine ⟨Pc, hPc, ?_⟩
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ A₀ 8
  obtain ⟨U', -⟩ := GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8)
    U₀.toUnifPre
  have hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁)) := by
    have := A'.isAb.proper
    have e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp
  obtain ⟨w, -, hw, -, -, hwL, -⟩ := GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW
  have hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L) := by rw [hPc]; exact hwL
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc
  have hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A) :=
    by
      have h := D'.toPre.P.isAb
      have := h.comm
      have := h.smooth
      have := h.proper
      have := h.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change IsProper (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change GeometricallyConnected (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'
  have hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _
  have : Smooth (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.smooth
    change Smooth (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have : GeometricallyConnected (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.geomConnected
    change GeometricallyConnected (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have := Q₀.i_hom
  letI := D'.toPre.addX
  haveI := D'.toPre.freeX
  haveI := D'.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X
    (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom
  haveI := hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀
    (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s
  exact ⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

end GlobalTheory.PowE8
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

theorem exists_symplectic_labels : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  intro W hW gQ
  refine ⟨E8Fibration.Lab.labMat W hW.2 gQ, ?_⟩
  intro l hl hlo j hj K _ _ k₀ hk₀ hlK P' hg B _ _ M pr hPP hP hE act hact hacts
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hNK : (((l ^ j) ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ (pow_ne_zero _ hlK)
  have hNodd : Odd ((l ^ j) ^ 2) := (hlo.pow).pow
  have hNpos : 0 < (l ^ j) ^ 2 := hNodd.pos
  have hN0 : (((l ^ j) ^ 2 : ℕ) : k₀) ≠ 0 := fun h => hNK (by simpa using congrArg k₀.subtype h)
  haveI : NeZero (((l ^ j) ^ 2 : ℕ) : k₀) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ((l ^ j) ^ 2) k₀)
    (Polynomial.degree_cyclotomic_pos _ k₀ hNpos).ne'
  have hp : IsPrimitiveRoot ζ ((l ^ j) ^ 2) := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  let bT : TBase k₀ ((l ^ j) ^ 2) := ⟨(hp.isUnit hNpos.ne').unit, hN0.isUnit, fun K' _ β => hp.map_of_injective β.injective⟩
  let z : Kˣ := Units.map k₀.subtype.toMonoidHom bT.ζ
  have hz : IsPrimitiveRoot z ((l ^ j) ^ 2) := IsPrimitiveRoot.coe_units_iff.1 (bT.prim K k₀.subtype)
  have hu : unitS (spMap k₀.subtype) bT.ζ = unitOn z := by
    ext
    simp only [unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, z]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom k₀.subtype)
    exact (congrArg (fun f => f.hom (bT.ζ : k₀)) this).symm
  obtain ⟨b, hb, hpair⟩ := GlobalTheory.T.exists_symplecticBasis_e8Factor_torsion W hW gQ _ hNodd K hNK z hz P' hg B pr hP
    (GlobalTheory.T.weilPairing_e8Power_depends_on_form W hW gQ K P' B M pr hPP hP hE _ hNpos)
  have := P'.isAb.comm
  obtain ⟨htor, hactc⟩ := GlobalTheory.T.e8_prod_torsion_section_bound W hW gQ P'.A B pr hP ((l ^ j) ^ 2) b hb
  have hpt : ∀ i i', Out.WeilIs P'.A P'.L ((l ^ j) ^ 2 : ℕ)
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)))
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))) (unitOn z ^ Out.stdSymp (8 * gQ) i i') := by
    intro i i'
    have h1 := hpair (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))
      _ _ (E8Fibration.Lab.ptOf_pr hP b _) (E8Fibration.Lab.ptOf_pr hP b _)
    have h2 := E8Fibration.Lab.isSharpBasis_sharpBasis W hW.2 gQ i i'
    simp only [E8Fibration.e8] at h1
    rw [h2] at h1
    exact_mod_cast h1
  refine ⟨bT, fun i => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)), htor, ?_, ?_, ?_⟩
  · intro K' _ _ x y hy
    have key := GlobalTheory.symplectic_system_torsion_basis L1 K P' ((l ^ j) ^ 2) z
    revert key
    generalize P'.g = g' at hg ⊢
    subst hg
    intro key
    exact key _ hNK hz htor hpt K' x y hy
  · intro i i'
    rw [hu]
    exact hpt i i'
  · intro a i
    exact hactc act hacts a i

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta | exact GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta | (intros; apply GlobalTheory.Poinc.IntTerm.term_eq_const_psi_theta <;> assumption)
end
