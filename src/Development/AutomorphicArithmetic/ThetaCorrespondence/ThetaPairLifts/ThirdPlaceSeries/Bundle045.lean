module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle427
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle036
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle039
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle042
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle004
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Formalism.LocalToGlobal.HilbertRowConditions.Bundle001
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.SharpRestriction.Divisibility.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
end GlobalTheory.HeightCounting.FormsStep
namespace GlobalTheory.HeightCounting.FormsStep
theorem hkB_charpoly_splits_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  classical
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P hfr hfi hP
  by_cases hc : HkCond D T i j k P
  · have hB : ∀ x ∈ BI D T S In i j b, x ∈ V0T D T S In.rho In.chi In.θ i j b := fun x hx => hx.2
    have hL1 := _root_.GlobalTheory.T.fixed_space_le_iSup_eigenspace_of_goodness D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b k P hc
    let ev : D.what₂.FT → FractionRing (T.O i) := fun σ =>
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)
    let sG : Finset D.what₂.FT := Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ
    have hle : (⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
        Module.End.eigenspace (hkT D T S In i j b k P) (ev σ)) ≤
        ⨆ r ∈ sG.image ev, Module.End.eigenspace (hkT D T S In i j b k P) r :=
      iSup₂_le fun σ hσ => le_iSup₂_of_le (ev σ) (Finset.mem_image_of_mem ev (by simpa [sG] using hσ)) le_rfl
    obtain ⟨m, hm⟩ := charpoly_restrict_map_eq_prod (BI D T S In i j b) (hkT D T S In i j b k P)
      (fun x hx => hst i j b k P hc x hx) (sG.image ev) (fun x hx => hle (hL1 (hB x hx)))
    refine ⟨m, ?_⟩
    have he : hkB D T S In hst i j b k P = ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict
        (fun x hx => hst i j b k P hc x hx) := by
      unfold hkB
      rw [dite_eq_left hc]
    rw [he]
    exact hm
  · have he : hkB D T S In hst i j b k P = 1 := by
      unfold hkB
      rw [dite_eq_right hc]
    refine ⟨Multiset.replicate (Module.finrank (T.O i) ↥(BI D T S In i j b)) 1, ?_⟩
    rw [he, LinearMap.charpoly_one, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, map_one]
end GlobalTheory.HeightCounting.FormsStep
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.type_orthogonality_of_form' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  first | exact @_root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt | exact _root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt | (intros; apply _root_.GlobalTheory.ThetaExh.typeOrth_of_pin_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.eventually_conjunction_mono_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (_root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂) ∧ (_root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
  first | exact @_root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | exact _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt | (intros; apply _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_automorphic_vector_satake_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  exact _root_.GlobalTheory.IsoComp.main_alt_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_mu_unit_eq_mu0_loc_k : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  exact _root_.GlobalTheory.TupleCharAtType.mu_unit_value_eq_loc_k_mu0
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.double_coset_support_at_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  first | exact @_root_.GlobalTheory.LocEigAgree.main_alt_alt | exact _root_.GlobalTheory.LocEigAgree.main_alt_alt | (intros; apply _root_.GlobalTheory.LocEigAgree.main_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : GlobalTheory.SplitRead.Reading P.T) :
    _root_.GlobalTheory.NPin.IsFaithfulReading P S →
      ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)),
        GlobalTheory.SplitWeil.IsTame (S i (D.naut.plGw k v) hw).mu :=
  _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.locations_distinguished_by_generics_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w → ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'), (i = i' ↔ ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) - iotaO L.X.nd L.Y.naut i' ((L.X.nd.hT i' v k : L.X.nd.X i' → L.X.nd.O i') x') ∈ (A.pl.plB w).nonunits) := by
  first | exact @_root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt | exact _root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt | (intros; apply _root_.GlobalTheory.CoefDuty.sameLoc_iff_heckeCong_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.type_tame_of_tame_not_unram : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  first | exact @_root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | exact _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | (intros; apply _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt <;> assumption)
end
end

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

abbrev _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace : Prop :=  ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (μ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hμ : GlobalTheory.SmGL.IsSmoothChar μ), GlobalTheory.SplitWeil.IsTame μ → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1) → ∀ c : ZMod (D.host.g k), D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) c) = ((μ (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 μ hμ) = X - C c
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}
structure TiedDataSAlt (ex : Extra D L hT Gi Gl K Y cX) where
  host : Host.HostTied D
  level : Host.LevelTied D
  cols : Forms.ColsTiedSym D
  full : Forms.ColsFullS cols
  extra : Forms.ColsExtraTiedS full ex
  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA
  twIn : TwIn D
  n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn
  frameN : Host.SameFrameN host n.gal.fr.jE
  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th
  chrVal : Host.ValLL0 D n.cf
  chrDt : Host.DtTied D n.cf
  chrN : Host.NCharTied D n.cf ex.nch n.tp
  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp
  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp
  sameChr : JoinChr.SameChr theta.T thetaChr
  what₂ : Rows.RowsCompatible D host n.cf n.tp
  inK : Y.Lev → ℕ → Prop
  geo : Geo.GeoTiedP Y inK
  tw : Forms.SymmetricTwistedColumnsAtPrimes n.tp cols ex.tw
  emt : Rows.EMtTied D cols tw
  g : G.GroupCompatibilityAll D hT ex.cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (cols.forms u).to0
def ExtraDataSelfDual (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (_root_.Formalism.L2.TiedDataSAlt ex)
end
def SecondChernLinkedClass : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, _root_.Formalism.L2.ExtraDataSelfDual (Fm.ex x hx i)
def LinkedFamiliesFixedValues' : FamClass := Formalism.MainNotions.WithPage _root_.Formalism.L2.SecondChernLinkedClass
def LinkedFamiliesAligned' : FamClass := fun {_} Fm =>
  _root_.Formalism.L2.LinkedFamiliesFixedValues' Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧
    Formalism.MainNotions.TameDistinctF Fm
end Formalism.L2
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_character_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  first | exact @_root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt | exact _root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt | (intros; apply _root_.GlobalTheory.ChiExtend.chi_eq_of_ext_alt <;> assumption)
end
end
