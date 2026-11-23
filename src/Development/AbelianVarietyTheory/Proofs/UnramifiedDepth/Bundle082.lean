module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle121
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle040
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.IncomingBounds.Bundle001
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ChartCharacters

section Unif

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UnifAfterExt

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] (G : Over (Sp W)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, E, ⟨d⟩⟩ := exists_finite_split _ h₀
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, e, he⟩ := GlobalTheory.T.exists_finite_dvr_extension_embedding_residueField W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') := RingHom.ext he
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e) E _ d)⟩

theorem exists_finite_ext_pelUnif {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (tK : SAB H (Sp T.Fr))
    (mK : SABMap tK t (jK T.V)) (x : Sp T.Fr ⟶ Xo.X) (mx : SABMap tK Xo.univ.t x) :
    ∃ (T' : Formalism.L2.Pj.CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)) (_ : SABMap t' t (spMap φ)),
      Function.Injective φ ∧ φ.Finite ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := exists_split_baseChange T.V t.G t.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  obtain ⟨t', m, hS'⟩ : ∃ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap (algebraMap T.V W))),
      ∃ S : SplitExt (Sp (ResidueField W)), S.IsGt ((Over.pullback (spMap (residue W))).obj t'.G) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V W)) t
    exact ⟨_, m, hS⟩
  obtain ⟨gam, hsq⟩ := exists_generic_square (algebraMap T.V W) hi
  have hp := polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK W) gam hsq
  obtain ⟨-, P, -⟩ := isOpen_and_uniformised W hc t' hp hS'
  exact ⟨{ V := W }, algebraMap T.V W, t', m, hi, RingHom.finite_algebraMap.2 hf, ⟨P⟩⟩

end Unif

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.CharDepth

open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw

section Map

variable {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {dd : ℕ}

end Map

end GlobalTheory.ChartCharacters
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianLift

private theorem exists_odd_prime_ne (p : ℕ) : ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p := by
  by_cases h : p = 3
  · exact ⟨5, by norm_num, by decide, by omega⟩
  · exact ⟨3, by norm_num, by decide, fun e => h e.symm⟩

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h1 R' _ π hπ hker
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have : IsLocalRing O := by
    have : ValuationRing O := ValuationRing.of_integers v hv
    infer_instance
  obtain ⟨n, hn, hodd, hnp⟩ := exists_odd_prime_ne p
  obtain ⟨j, hj⟩ := GlobalTheory.ZM.SiegelLargeLevel.exists_siegelFamily_sRep GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1
    GlobalTheory.AbLaw.CubeAssembly.cube_gen GlobalTheory.thetaUnifAV_all P.g n h1 hn hodd
  obtain ⟨Ag, hAg⟩ := hj j le_rfl p hp hnp
  have hM0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hcop : ((n ^ j) ^ 2).Coprime p :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hn hp).2 hnp))
  generalize (n ^ j) ^ 2 = M at Ag hAg hM0 hcop
  obtain ⟨β, hβ, hMu, hprim⟩ := GlobalTheory.exists_zp_ringHom_integers p C v O hv M hM0 hcop
  have hζ : β (Geo.Tor.zetaZP p M) ^ M = 1 := hinj (by
    rw [map_pow, map_one]; exact (hprim C (algebraMap O C)).pow_eq_one)
  let ze : Oˣ := (IsUnit.of_pow_eq_one hζ hM0).unit
  have hze : (ze : O) = β (Geo.Tor.zetaZP p M) := rfl
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := GlobalTheory.exists_level_over_integers p C v O hv T P₀ io P φ hφ hL hg P.g M ze rfl hMu
    (hprim C (algebraMap O C))
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre O T P₀ io P φ hφ hL hg _ β P.g M (Geo.Tor.zetaZP p M) ze lev rfl hMu hze
    hprim hl₁ hl₂ hl₃
  obtain ⟨β', c', hc', φ₁, φ₂, hpb, hsq, hiso, -⟩ :=
    GlobalTheory.SiegelLift.exists_principal_lift P.g p M Ag hAg hcop hM0 O R' π hπ hker β hβ c hc
  let k : P.A ⊗ P.A ⟶ c.A ⊗ c.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  have hk : k.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [k]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨c'.A, c'.grp, c'.comm, c'.P, e.inv.left ≫ φ₁, k.left ≫ φ₂, c'.ab, c'.isLB, c'.rig₁, c'.rig₂, c'.symm,
    hc'.1, hc'.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact ((Geo.Tor.isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : Geo.Tor.LBIso (abelian₂ P.A P.L) (c.P.pull k.left) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullSec _ _ k.left hk) (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        hcP.symm
    have hB : Geo.Tor.LBIso (c.P.pull k.left) (c'.P.pull (k.left ≫ φ₂)) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        (Geo.Tor.chartPullSame c'.P _ (fun _ => φ₂) _ k.left fun _ => rfl) hiso
    exact Geo.Tor.LBIso.trans (DVR.linComb_isLB _ P.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _)
      (DVR.linComb_isLB _ c'.isLB _ _) hA hB

end GlobalTheory.AbelianLift
end
