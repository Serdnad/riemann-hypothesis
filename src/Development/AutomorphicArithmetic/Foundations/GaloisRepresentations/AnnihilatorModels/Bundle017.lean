module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle627
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftPt_of :
    LiftPt := by
  intro V _ _ _ _ B _ _ _ _ χ hχ
  classical
  let m : Ideal B := RingHom.ker χ
  haveI : m.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨q, hqmin, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : q.IsPrime := hqmin.1.1
  have hnzd : ∀ v : V, v ≠ 0 → algebraMap V B v ∈ nonZeroDivisors B := by
    intro v hv
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
    · rw [← Algebra.commutes, ← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left hv
  have hinj : Function.Injective (algebraMap V (B ⧸ q)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hqmin) hv (hnzd v hv0)
  have hK : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V (FractionRing V)
  haveI : Module.IsTorsionFree V (B ⧸ q) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hinj (by rw [h, map_zero])
  haveI : Module.IsTorsionFree V (FractionRing V) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun h => hK (by rw [h, map_zero])
  haveI : Algebra.IsIntegral V (B ⧸ q) := inferInstance
  haveI : Algebra.IsAlgebraic V (B ⧸ q) := Algebra.IsIntegral.isAlgebraic
  let φ : (B ⧸ q) →ₐ[V] FractionRing V := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hker : RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := V)
    ext v
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, RingHom.coe_coe, AlgHom.commutes]
    exact map_eq_zero_iff _ hK
  have hφinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ RingHom.ker (φ : (B ⧸ q) →+* FractionRing V) := hx
    rwa [hker] at this
  let ψ : B →ₐ[V] FractionRing V := φ.comp (Ideal.Quotient.mkₐ V q)
  have hψ : ∀ b, ψ b ∈ (⊥ : Subalgebra V (FractionRing V)) := by
    intro b
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((Algebra.IsIntegral.isIntegral (R := V) (Ideal.Quotient.mkₐ V q b)).map φ)
    exact ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective hK
  let z : B →ₐ[V] V := e.toAlgHom.comp (ψ.codRestrict ⊥ hψ)
  have hz : ∀ b, algebraMap V (FractionRing V) (z b) = ψ b := by
    intro b
    have h1 := e.symm_apply_apply (ψ.codRestrict ⊥ hψ b)
    have h2 := e.symm.commutes (z b)
    have h3 : (algebraMap V V) (z b) = e (ψ.codRestrict ⊥ hψ b) := rfl
    rw [h3, h1] at h2
    have h4 := congrArg (fun s : (⊥ : Subalgebra V (FractionRing V)) => (s : FractionRing V)) h2
    simpa using h4.symm
  refine ⟨z, ?_⟩
  ext b
  have hc : b - algebraMap V B (z b) ∈ q := by
    have h0 : z (b - algebraMap V B (z b)) = 0 := by
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h1 : ψ (b - algebraMap V B (z b)) = 0 := by
      rw [← hz, h0, map_zero]
    have h2 : Ideal.Quotient.mkₐ V q (b - algebraMap V B (z b)) = 0 :=
      hφinj (by rw [map_zero]; exact h1)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  have hm : χ (b - algebraMap V B (z b)) = 0 := hqm hc
  rw [map_sub, sub_eq_zero] at hm
  rw [hm, ← RingHom.comp_apply, hχ]
  rfl
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repOfFF_of :
    AlgOf → RepOfFF := by
  rintro hA κ _ A P ⟨K, i, hm, hfin, hfl, hP⟩
  obtain ⟨B, _, _, k, hf, hfr, pb⟩ := hA (Sp κ) K.left K.hom hfin hfl κ (𝟙 _)
  have hk : IsIso k := pb.isIso_fst_of_isIso
  have hw : k ≫ K.hom = spMap (algebraMap κ B) := by
    simpa using pb.w
  let e : algPt κ B ≅ K := Over.isoMk (asIso k) hw
  refine ⟨Module.finrank κ B, B, ‹_›, ‹_›, hf, hfr, rfl, e.hom ≫ i, inferInstance, fun T g => ?_⟩
  rw [← hP T g]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.hom, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.inv, by simpa using hy⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobHom_of :
    FrobHom := by
  intro p f hp κ _ _ φ hφ A A' _ _ ψ hpull h
  obtain ⟨hpb, hmul⟩ := hpull
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := by
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (CharP.cast_eq_zero κ p)
    rw [map_natCast, map_zero] at e
    exact e
  have hfrκ : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hsq : GlobalTheory.SS.FrobField.absFrob A.left p f hp h ≫ A.hom = A.hom ≫ spMap φ := by
    rw [GlobalTheory.SS.FrobField.absFrob_nat A.hom p f hp h hκ, hfrκ]
  let F : A ⟶ A' := Over.homMk (hpb.lift (GlobalTheory.SS.FrobField.absFrob A.left p f hp h) A.hom hsq)
    (hpb.lift_snd _ _ _)
  have hFψ : F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h := hpb.lift_fst _ _ _
  have hTz : ∀ T : Over (Sp κ), ((p : ℕ) : Γ(T.left, ⊤)) = 0 := fun T =>
    GlobalTheory.SS.FrobField.cast_zero_of_hom T.hom hκ
  have key : ∀ (T : Over (Sp κ)) (x : T ⟶ A),
      (x ≫ F).left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ x.left := by
    intro T x
    rw [Over.comp_left, Category.assoc, hFψ]
    exact (GlobalTheory.SS.FrobField.absFrob_nat x.left p f hp (hTz T) h).symm
  let Fr : ∀ T : Over (Sp κ), Over.mk (T.hom ≫ spMap φ) ⟶ T := fun T =>
    Over.homMk (GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T)) (by
      simp only [Over.mk_hom]
      rw [GlobalTheory.SS.FrobField.absFrob_nat T.hom p f hp (hTz T) hκ, hfrκ])
  haveI hF : IsMonHom F := by
    apply isMonHom_of_mul F
    intro T x y
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [← hmul T (x ≫ F) (y ≫ F) (Fr T ≫ x) (Fr T ≫ y) (by rw [key]; rfl) (by rw [key]; rfl),
        ← MonObj.comp_mul, key, Over.comp_left]
      rfl
    · rw [Over.w, Over.w]
  refine ⟨F, hF, hFψ, fun T g => ?_⟩
  have hone : (1 : T ⟶ A').left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ (1 : T ⟶ A).left := by
    rw [← MonObj.one_comp (X := T) F, key]
  constructor
  · intro hg h'
    have e := congrArg (fun k => k.left ≫ ψ) hg
    rw [key, hone] at e
    exact e
  · intro hk
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [key, hone]
      exact hk (hTz T)
    · rw [Over.w, Over.w]
end

section

noncomputable section

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_algHom_ker (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B]
    [Module.Finite κ B] (p : PrimeSpectrum B) :
    ∃ ε : B →ₐ[κ] κ, RingHom.ker ε.toRingHom = p.asIdeal := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
  letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb
  refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩
  ext x
  change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem ringHomog_of : RingHomog := by
  intro κ B _ _ _ _ _ ε₀ _ hτ
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) :=
    Module.Finite.of_surjective
      (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap
      (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)))
  have hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
        (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞) := by
    intro p
    obtain ⟨ε, hε⟩ := exists_algHom_ker κ B p
    obtain ⟨τ, hτε⟩ := hτ ε
    rw [GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]
    have hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom =
        (RingHom.ker ε₀.toRingHom).primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨τ.symm y, ?_, ?_⟩
        · simpa using hy
        · simp
    exact GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)
  have h := GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm
  rw [← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B] at h
  exact_mod_cast h

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem count_eq (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (hab : IsAbelianScheme A)
    (K : Over S) (i : K ⟶ A) (hm : Mono i) (hfin : IsFinite K.hom) (hfl : Flat K.hom) (c : ℕ) (hi : i ^ c = 1)
    (P : ∀ T : Over S, (T ⟶ A) → Prop) (hP : ∀ (T : Over S) (g : T ⟶ A), InSub i g ↔ P T g)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (hc : (c : V) ≠ 0)
    (z : Sp V ⟶ S) (B : Type) [CommRing B] [Algebra V B] [Module.Finite V B] [Module.Free V B] (k : Sp B ⟶ K.left)
    (hk : IsPullback k (spMap (algebraMap V B)) K.hom z) :
    Module.finrank V B = Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} := by
  haveI := hfin
  haveI := hfl
  have hcF : ((c : FractionRing V)) ≠ 0 := by
    intro h
    apply hc
    apply IsFractionRing.injective V (FractionRing V)
    simpa using h
  let pt : Sp (FractionRing V) := (⊥ : PrimeSpectrum (FractionRing V))
  have h1 := GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points S A hab K i c hm hfin hfl hi (FractionRing V) hcF
    (spMap (algebraMap V (FractionRing V)) ≫ z) pt
  have h2 := Scheme.Hom.finrank_of_isPullback k (spMap (algebraMap V B)) K.hom z hk
    (spMap (algebraMap V (FractionRing V)) pt)
  have h3 := Scheme.Hom.finrank_SpecMap_algebraMap V B (spMap (algebraMap V (FractionRing V)) pt)
  rw [Scheme.Hom.comp_apply] at h1
  have h4 : Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} =
      Nat.card (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ K) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g ≫ i, (hP _ _).1 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩).symm
    · intro a b hab'
      exact (cancel_mono i).1 (congrArg Subtype.val hab')
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hP _ _).2 hg
      exact ⟨y, Subtype.ext hy⟩
  rw [h4, ← h1, ← h2]
  unfold spMap at h3 ⊢
  rw [h3, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem fFRead_of : AlgOf → FFRead := by
  intro hAlg S A _ _ hab P hRep c hc V _ _ _ _ hcV z A' φ hpb P' hP'
  obtain ⟨K, i, hm, hfin, hfl, hiP⟩ := hRep
  haveI := hfin
  haveI := hfl
  have hi : i ^ c = 1 := hc K i ((hiP K i).1 ⟨𝟙 _, by simp⟩)
  obtain ⟨BV, _, _, kV, _, _, hkV⟩ := hAlg S K.left K.hom hfin hfl V z
  have hcount := count_eq S A hab K i hm hfin hfl c hi P hiP V hcV z BV kV hkV
  obtain ⟨Bk, _, _, kk, _, _, hkk⟩ :=
    hAlg S K.left K.hom hfin hfl (IsLocalRing.ResidueField V) (resPt V ≫ z)
  have hr : Module.finrank (IsLocalRing.ResidueField V) Bk = Module.finrank V BV := by
    let q : Sp (IsLocalRing.ResidueField V) := (⊥ : PrimeSpectrum (IsLocalRing.ResidueField V))
    have e1 := Scheme.Hom.finrank_of_isPullback kk _ K.hom (resPt V ≫ z) hkk q
    have e2 := Scheme.Hom.finrank_of_isPullback kV _ K.hom z hkV (resPt V q)
    have e3 := Scheme.Hom.finrank_SpecMap_algebraMap (IsLocalRing.ResidueField V) Bk q
    have e4 := Scheme.Hom.finrank_SpecMap_algebraMap V BV (resPt V q)
    rw [Scheme.Hom.comp_apply] at e1
    unfold spMap at e1 e2
    rw [e3, Module.rankAtStalk_eq_finrank_of_free] at e1
    rw [e4, Module.rankAtStalk_eq_finrank_of_free] at e2
    exact e1.trans e2.symm
  have wsq : (kk ≫ i.left) ≫ A.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) ≫ (resPt V ≫ z) := by
    rw [Category.assoc, Over.w i]
    exact hkk.w
  have hlf : hpb.lift _ _ wsq ≫ φ = kk ≫ i.left := hpb.lift_fst _ _ wsq
  have hls : hpb.lift _ _ wsq ≫ A'.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) :=
    hpb.lift_snd _ _ wsq
  have hlm : Mono (hpb.lift _ _ wsq) := by
    constructor
    intro X a b hab'
    apply hkk.hom_ext
    · haveI := Over.mono_left_of_mono i
      have h1 := congrArg (· ≫ φ) hab'
      simp only [Category.assoc, hlf] at h1
      simpa only [Category.assoc] using (cancel_mono i.left).1 (by simpa only [Category.assoc] using h1)
    · have h1 := congrArg (· ≫ A'.hom) hab'
      simpa only [Category.assoc, hls] using h1
  refine ⟨Bk, inferInstance, inferInstance, inferInstance, inferInstance, hr.trans hcount,
    Over.homMk (U := Over.mk (spMap (algebraMap (IsLocalRing.ResidueField V) Bk))) (hpb.lift _ _ wsq) hls,
    ?_, ?_⟩
  · constructor
    intro X a b hab'
    ext
    exact (cancel_mono (hpb.lift _ _ wsq)).1 (by simpa using congrArg Over.Hom.left hab')
  · intro T g
    have hw : (g.left ≫ φ) ≫ A.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w g]
      rfl
    rw [hP' T g (Over.homMk (g.left ≫ φ) hw) rfl, ← hiP]
    constructor
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw2 : (y.left ≫ kk) ≫ K.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
        rw [Category.assoc, hkk.w]
        simpa using congrArg (· ≫ resPt V ≫ z) (Over.w y)
      refine ⟨Over.homMk (y.left ≫ kk) hw2, ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [← hyl, Category.assoc, hlf]
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw3 : y.left ≫ K.hom = T.hom ≫ resPt V ≫ z := by
        simpa using Over.w y
      refine ⟨Over.homMk (hkk.lift y.left T.hom hw3) (by simpa using hkk.lift_snd _ _ hw3), ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left]
      apply hpb.hom_ext
      · rw [Category.assoc, hlf, ← Category.assoc, hkk.lift_fst, hyl]
      · rw [Category.assoc, hls, hkk.lift_snd]
        simpa using (Over.w g).symm

end UpperTheory.Gal.crystallineComparison.Mod
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem comp_pow' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : f ≫ (g ^ n) = (f ≫ g) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem pow_comp' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom g] (n : ℕ) : (f ^ n) ≫ g = (f ≫ g) ^ n := by
  exact map_pow (IsMonHom.monoidHom g X) f n

theorem UpperTheory.Gal.crystallineComparison.Mod.isogComp_of :
    PairCalc → IsogComp := by
  intro hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2
  obtain ⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩ := h1
  obtain ⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩ := h2
  haveI := hψ
  haveI := hχ
  haveI := hψ'
  haveI := hχ'
  refine ⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩
  · intro a
    rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro x
    rw [he', he, Category.assoc]
  · rw [(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]
    intro T x y
    have e1 := ((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL
    have e2 := ((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'
    rw [← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]
  · rw [Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1,
      ← pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2,
      ← pow_mul, mul_comm]
end
