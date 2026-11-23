module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3264
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbChart

theorem exists_siegPre_localization : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := fun g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ p _ hp κ s' hκ hs =>
  GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p (GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus R G₁ hG p hp) κ s' hκ hs

theorem exists_spMap_ext : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (b : cycAway n →+* R) (x : Sp (FractionRing R) ⟶ Sp (cycAway n)), ∃ s : Sp R ⟶ Sp (cycAway n), jK R ≫ s = x := by
  intro n R _ _ _ b x
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* FractionRing R, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  let A := algebraMap R (FractionRing R)
  have hAi : Function.Injective A := IsFractionRing.injective R (FractionRing R)
  have hgen : ∀ (w : ℂ) (hw : w ∈ cycAway n), φ ⟨w, hw⟩ ∈ A.range := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨zeta 0, Subring.subset_closure (Or.inl rfl)⟩ : cycAway 0) = 1 := Subtype.ext (by simp [zeta])
          rw [this, map_one]; exact A.range.one_mem
        · have hpow : (⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩ : cycAway n) ^ n = 1 :=
            Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one)
          have hI : IsIntegral R (φ ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩) := by
            refine IsIntegral.of_pow hn ?_
            rw [← map_pow, hpow, map_one]; exact isIntegral_one
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
          exact ⟨r, hr⟩
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway 0) = 0 := Subtype.ext (by simp)
          rw [this, map_zero]; exact A.range.zero_mem
        · set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
          have hu : u * (n : cycAway n) = 1 := Subtype.ext (by simp [u, hn.ne'])
          have e1 : φ u * (n : FractionRing R) = 1 := by rw [← map_natCast φ, ← map_mul, hu, map_one]
          have e2 : A (b u) * (n : FractionRing R) = 1 := by rw [← map_natCast A, ← map_mul, ← map_natCast b, ← map_mul, hu, map_one, map_one]
          have hn0 : (n : FractionRing R) ≠ 0 := right_ne_zero_of_mul_eq_one e1
          exact ⟨b u, mul_right_cancel₀ hn0 (e2.trans e1.symm)⟩
    | zero => exact ⟨0, by rw [map_zero]; exact (map_zero φ).symm⟩
    | one => exact ⟨1, by rw [map_one]; exact (map_one φ).symm⟩
    | add w v hw hv ihw ihv =>
      have : (⟨w + v, add_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ + ⟨v, hv⟩ := rfl
      rw [this, map_add (f := _)]; exact A.range.add_mem ihw ihv
    | neg w hw ih =>
      have : (⟨-w, neg_mem hw⟩ : cycAway n) = -⟨w, hw⟩ := rfl
      rw [this, map_neg]; exact A.range.neg_mem ih
    | mul w v hw hv ihw ihv =>
      have : (⟨w * v, mul_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ * ⟨v, hv⟩ := rfl
      rw [this, map_mul]; exact A.range.mul_mem ihw ihv
  let e : R ≃+* A.range := RingEquiv.ofBijective A.rangeRestrict ⟨fun a a' h => hAi (congrArg Subtype.val h), A.rangeRestrict_surjective⟩
  let ψ : cycAway n →+* R := (e.symm : A.range →+* R).comp (φ.codRestrict A.range fun z => hgen z.1 z.2)
  have hψ : A.comp ψ = φ := by
    ext z
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hgen z.1 z.2⟩)
    exact h
  refine ⟨spMap ψ, ?_⟩
  exact (spMap_comp ψ A).symm.trans (congrArg spMap hψ)

theorem asIdeal_eq_bot_of_charZero : ∀ (n : ℕ) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ Sp (cycAway n)) (q : Sp K), (x q).asIdeal = ⊥ := by
  intro n K _ _ x q
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* K, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  change Ideal.comap φ q.asIdeal = ⊥
  rw [hq, ← RingHom.ker_eq_comap_bot]
  by_contra hne
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have halg : IsAlgebraic ℤ a := by
    have hC : ∀ z ∈ cycAway n, IsIntegral ℚ z := by
      intro z hz
      refine Subring.closure_le (t := (integralClosure ℚ ℂ).toSubring) |>.2 ?_ hz
      rintro w (rfl | rfl)
      · show IsIntegral ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using (isIntegral_one : IsIntegral ℚ (1 : ℂ))
        · exact ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top
      · show IsIntegral ℚ ((n : ℂ)⁻¹)
        simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := ((n : ℚ)⁻¹)))
    have h1 : IsAlgebraic ℚ (a : ℂ) := (hC a a.2).isAlgebraic
    have h2 : IsAlgebraic ℤ (a : ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h1
    exact (isAlgebraic_algHom_iff ((cycAway n).subtype.toIntAlgHom) Subtype.val_injective).1 h2
  have := Ideal.comap_ne_bot_of_algebraic_mem ha0 ha halg
  apply this
  rw [eq_bot_iff]
  intro m hm
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hm
  exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 hm)

theorem mem_range_of_mem_abLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy p hp
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have hu : ∀ x : p.asIdeal.primeCompl, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R)
      (⟨x.1, mem_nonZeroDivisors_of_ne_zero (fun h => x.2 (h ▸ p.asIdeal.zero_mem))⟩ : nonZeroDivisors R)
  let lf : Localization.AtPrime p.asIdeal →+* FractionRing R := IsLocalization.lift hu
  let ιp := spMap (algebraMap R (Localization.AtPrime p.asIdeal))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal) := spMap lf
  have hκ : κ ≫ ιp = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hnorm := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨s, hs⟩ := exists_spMap_ext n R b (y ≫ F.s)
  have hs' : κ ≫ ιp ≫ s = y ≫ F.s := by rw [← Category.assoc, hκ, hs]
  obtain ⟨c, c', hc, m₁, m₂⟩ := exists_siegPre_localization g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p hp κ (ιp ≫ s) hκ hs'
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.AtPrime p.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors p.asIdeal)).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hdense : Dense {x : Sp (Localization.AtPrime p.asIdeal) | ((ιp ≫ s) x).asIdeal = ⊥} := by
    refine Dense.mono ?_ hdom.denseRange
    rintro _ ⟨q, rfl⟩
    show ((ιp ≫ s) (κ q)).asIdeal = ⊥
    rw [← Scheme.Hom.comp_apply, hs']
    exact asIdeal_eq_bot_of_charZero n (FractionRing R) (y ≫ F.s) q
  obtain ⟨f, hfs, hf⟩ := F.rep _ (ιp ≫ s) c inferInstance hdense hc
  have hfy : κ ≫ f = y := F.inj (FractionRing R) (κ ≫ f) y (y ≫ F.s) c'
    (by rw [Category.assoc, hfs, hs']) (GlobalTheory.SiegelPullComp.pb_comp hf m₁) m₂
  have hξ : ιp ≫ ξ = f ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hfy]
  refine ⟨f (closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩
  change (f ≫ j) (closedPoint _) = ξ p
  rw [← hξ]
  change ξ (ιp (closedPoint _)) = ξ p
  congr 1
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.AbChart
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.DivPotGood

theorem potGood_of_divisionAlgebra_action : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hact h1 hmul hadd B _ _ _ jj hdiv hinj hspan hgB
  obtain ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, hsa, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, i1, i2, i3, i4, i5, i6, i7, i8, hcomp, hfin, hloc, hcpl, G, iG, hmod, ?_⟩

  set f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  set A' := (Over.pullback f).obj A
  have hψ : IsGrpPullback A' A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨act₁, ⟨h1a, h1b, h1c, h1d⟩, -⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes (Sp K) (Sp L) f A A' _ hψ O act hact h1 hmul hadd
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hmod A' _ hψ
  obtain ⟨act₂, ⟨h2a, h2b, h2c, h2d⟩, -⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G A' φ hsa hφ O act₁ h1a h1b h1c h1d
  have hres : IsGrpPullback (GlobalTheory.SS.spFibre G) G (spMap (IsLocalRing.residue W)) (pullback.fst G.hom _) :=
    isGrpPullback_pullback G _
  obtain ⟨act₃, ⟨h3a, h3b, h3c, h3d⟩, -⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (IsLocalRing.residue W)) G (GlobalTheory.SS.spFibre G) _ hres O act₂ h2a h2b h2c h2d
  haveI : IsCommMonObj (GlobalTheory.SS.spFibre G) := by
    haveI := hsa.comm
    infer_instance
  obtain ⟨ρ, -⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action _ (GlobalTheory.SS.spFibre G) E O act₃ h3a h3b h3c h3d

  obtain ⟨e, -⟩ := hmod
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hA'g : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom f) hg
  have hGLg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (snd := ((Over.pullback (spMap (algebraMap W L))).obj G).hom)
        (f := A'.hom) (g := 𝟙 _) ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩) hA'g
  have hsc : GlobalTheory.SS.SmConn G := ⟨hsa.comm, hsa.smooth, hsa.separated, hsa.quasiCompact, hsa.geomConnected⟩
  have hsp : SmoothOfRelativeDimension g (GlobalTheory.SS.spFibre G).hom := GlobalTheory.IsogRed.relDim_spFibre (K := L) G hsc g hGLg
  have hle := GlobalTheory.T.finrank_torusExtension_characters_le_relDim _ (GlobalTheory.SS.spFibre G) E g hsp
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  have h0 : Module.finrank ℤ E.X = 0 := GlobalTheory.T.divisionAlgebra_order_no_small_lattice B O jj hdiv hinj hspan E.X ρ (lt_of_le_of_lt hle hgB)

  have hprop : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom f))
    rw [← Over.w e.hom]
    infer_instance
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsa hprop E h0

end GlobalTheory.DivPotGood
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped Matrix

namespace GlobalTheory.PotGoodLie

theorem proper_pull {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (hM : GlobalTheory.SS.IsModel (L := L) A G)
    (hA : IsAbelianScheme A) : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
  obtain ⟨e, -⟩ := hM
  have := hA.proper
  have h : ((Over.pullback (spMap (algebraMap W L))).obj G).hom = e.hom.left ≫ ((Over.pullback (spMap (algebraMap K L))).obj A).hom := (Over.w e.hom).symm
  rw [h]
  have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
    show IsProper (pullback.snd A.hom _)
    infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eq_one_of_lieMult_zero {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G)
    {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (h : LieMult a t τ 0) (w : epsPt t ⟶ G)
    (hw : IsLieEigen a t τ w) : w = 1 := by
  obtain ⟨v, -, H⟩ := h
  obtain ⟨c, ⟨u, -, hu⟩, -⟩ := H w hw
  simpa using hu

theorem lift_ext (V K W L Ω : Type) [CommRing V] [Field K] [CommRing W] [IsDomain W] [Field L] [Field Ω]
    [IsAlgClosed Ω] [Algebra V K] [Algebra V W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    (hc : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hfin : Module.Finite V W) (g : K →+* Ω) : ∃ g' : L →+* Ω, g'.comp (algebraMap K L) = g := by
  letI := g.toAlgebra
  have hint : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have halg : ∀ w : W, IsAlgebraic K (algebraMap W L w) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := hint.isIntegral w
    refine ⟨p.map (algebraMap V K), (hp.map _).ne_zero, ?_⟩
    have := congrArg (algebraMap W L) hpw
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← this, hc]
  haveI : Algebra.IsAlgebraic K L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    rw [div_eq_mul_inv]
    exact IsAlgebraic.mul (halg a) (IsAlgebraic.inv (halg b))
  exact ⟨(IsAlgClosed.lift : L →ₐ[K] Ω).toRingHom, by ext x; simp [RingHom.algebraMap_toAlgebra]⟩

theorem prod_of_add {A B J : Type} [AddCommMonoid A] [CommMonoid B] (φ : A → B) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) (s : Finset J) (g : J → A) : φ (∑ i ∈ s, g i) = ∏ i ∈ s, φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]

theorem exists_ringHom {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) {n : ℕ} (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R) {k : Type} [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X : Over S} (T : (Fin n → k) → (X ⟶ G)) (Tinj : Function.Injective T)
    (Tadd : ∀ c c', T (c + c') = T c * T c')
    (Tact : ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c)) :
    ∃ Mr : O →+* Matrix (Fin n) (Fin n) R, ∀ x, Mr x = M (a.act x) := by
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, (∀ c, T ((P.map f) *ᵥ c) = T ((Q.map f) *ᵥ c)) → P = Q := by
    intro P Q h
    apply Matrix.map_injective hf
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using Tinj (h c)
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have act0 : a.act 0 = 1 := by simpa using a.add 0 0
  refine ⟨{ toFun := fun x => M (a.act x), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun _ => rfl⟩
  · apply key; intro c
    rw [← Tact _ (a.hom 1), a.one]
    simp
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x * y)), mul_comm x y, a.mul, ← Category.assoc, Tact _ (a.hom y), Tact _ (a.hom x),
      Matrix.mulVec_mulVec, ← Matrix.map_mul]
  · apply key; intro c
    rw [← Tact _ (a.hom 0), act0, comp_one]
    simp [T0]
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x + y)), a.add, comp_mul, Tact _ (a.hom x), Tact _ (a.hom y), ← Tadd, Matrix.map_add _ (map_add f),
      Matrix.add_mulVec]

theorem finrank_zero (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (F : Type) [Field F] [NumberField F] (a : OAct (𝓞 F) G) (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] (f : W →+* Ω) (hf : Function.Injective f) (σ : 𝓞 F →+* Ω) (h0 : LieMult a (spMap f) σ 0)
    (E : TorusExtension (GlobalTheory.SS.spFibre G)) : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 := by
  classical
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI : IsCommMonObj G := hG.comm
  obtain ⟨n, M, -, hT⟩ := GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring W G hG.smooth
  obtain ⟨T, Tinj, Trange, Tadd, Tsc, Tact⟩ := hT Ω f
  obtain ⟨Mr, hMr⟩ := exists_ringHom a M f hf T Tinj Tadd Tact
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have hno : ∀ c : Fin n → Ω, (∀ x, ((Mr x).map f).mulVec c = σ x • c) → c = 0 := by
    intro c hc
    have hE : IsLieEigen a (spMap f) σ (T c) := by
      refine ⟨(Trange (T c)).2 ⟨c, rfl⟩, fun x => ?_⟩
      rw [Tact _ (a.hom x), ← hMr, hc, Tsc]
    exact Tinj ((eq_one_of_lieMult_zero a _ σ h0 _ hE).trans T0.symm)
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  obtain ⟨w, ⟨i0, hu⟩, hsum⟩ := GlobalTheory.T.exists_primitive_annihilator' F W Ω f hf n Mr σ hno _ b
  obtain ⟨ρ, U, Uinj, Ufst, Uadd, Usc, Uact⟩ := GlobalTheory.T.toric_part_fibre_lie_algebra_characters (Sp W) G (𝓞 F) a.act a.hom a.one a.mul a.add
    (ResidueField W) (spMap (residue W)) E
  obtain ⟨T', -, T'range, T'add, T'sc, T'act⟩ := hT (ResidueField W) (residue W)
  have T'0 : T' 0 = 1 := by simpa using T'add 0 0
  have U0 : U 0 = 1 := by simpa using Uadd 0 0
  refine GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor F E.X ρ (ResidueField W) _ b (fun i => residue W (w i)) ?_ ?_
  · intro h
    exact (residue_ne_zero_iff_isUnit _).2 hu (congrFun h i0)
  · intro l χ
    obtain ⟨c, hc⟩ := (T'range (U l)).1 (Ufst l)
    have step : ∀ i, U ((AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) =
        T' (residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c)) := by
      intro i
      have e : U (l.comp (ρ (b i)).toAddMonoidHom) = T' ((Mr (b i)).map (residue W) *ᵥ c) := by
        rw [← Uact, ← hc, T'act _ (a.hom _), hMr]
      apply Over.OverMorphism.ext
      rw [Usc, T'sc, e]
    have hv : ∑ i, residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c) = 0 := by
      have := congrArg (fun P => ((residue W).mapMatrix P) *ᵥ c) hsum
      have hsm : ∀ i, (w i • Mr (b i)).map (residue W) = residue W (w i) • (Mr (b i)).map (residue W) := by
        intro i; ext; simp

      simpa [map_sum, Matrix.sum_mulVec, hsm, Matrix.smul_mulVec] using this
    have hL : (∑ i, (AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) = 0 := by
      apply Uinj
      rw [prod_of_add U U0 Uadd, U0, Finset.prod_congr rfl (fun i _ => step i), ← prod_of_add T' T'0 T'add, hv, T'0]
    have := congrArg (fun m => m χ) hL
    simpa using this

theorem potGood_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA F _ _ act Ω _ _ g σ hL
  obtain ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, hsemi, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, ?_⟩
  have hAL := isGrpPullback_pullback A (spMap (algebraMap K L))
  obtain ⟨actL, ⟨h1, h2, h3, h4⟩, hLc⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (algebraMap K L)) A
    ((Over.pullback (spMap (algebraMap K L))).obj A) _ hAL (𝓞 F) act.act act.hom act.one act.mul act.add
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hM _ _ hAL
  obtain ⟨actG, ⟨g1, g2, g3, g4⟩, hGc⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G _ φ hsemi hφ (𝓞 F) actL h1 h2 h3 h4
  let aL : OAct (𝓞 F) ((Over.pullback (spMap (algebraMap K L))).obj A) := ⟨actL, h1, h2, h3, h4⟩
  let aG : OAct (𝓞 F) G := ⟨actG, g1, g2, g3, g4⟩
  obtain ⟨g', hg'⟩ := lift_ext V K W L Ω hc hfin g
  have e1 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ A _ _ (pullback.fst _ _) act aL hAL hLc Ω (spMap g') σ 0
  have hx : spMap g' ≫ spMap (algebraMap K L) = spMap g := by rw [← hg', spMap_comp]
  have e2 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ G _ _ φ aG aL hφ hGc Ω (spMap g') σ 0
  have hG0 : LieMult aG (spMap (g'.comp (algebraMap W L))) σ 0 := by
    rw [spMap_comp]
    exact e2.1 (e1.2 (hx ▸ hL))
  haveI : CharZero Ω := charZero_of_injective_ringHom g.injective
  have hinj : Function.Injective (g'.comp (algebraMap W L)) :=
    g'.injective.comp (IsFractionRing.injective W L)
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsemi (proper_pull A G hM hA) E
    (finrank_zero W G hsemi F aG Ω _ hinj σ hG0 E)

end GlobalTheory.PotGoodLie
end
