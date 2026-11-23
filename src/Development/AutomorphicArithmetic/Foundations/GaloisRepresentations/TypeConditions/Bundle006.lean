module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle001
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspAOfAb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalS

open Formalism.MainNotions.SumRepresentations Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))

private theorem exists_isCompl_finrank_inertia_of_charpoly (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k)) (hL : LGCatN N r A w)
    (hmult : ∀ x, rootMultiplicity (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))
      (((redRep N i (r x) (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) _).charpoly) = R.t)
    (x : N.X i) :
    ∃ U U' : Submodule (Qbar (N.l i)) (Fin R.nV → Qbar (N.l i)), IsCompl U U' ∧
      Module.finrank (Qbar (N.l i)) U' = R.t ∧
      ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        (∀ v ∈ U, ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v ∈ U) ∧
        ∀ v ∈ U', ((mapRep (iotaOQ N A i) (r x) γ : GL _ _) :
            Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).mulVec v = iotaOQ N A i (chi1 N i γ) • v := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hγ₀I : N.gam0 i w ∈ Ine (F := H.E) (N.plOm.1 w) := N.locNd_chebotarevPlace_mem i w
  have htame := (N.restN_tameGenerator_generates i w (Or.inl hS)).2
  have hcpQ : ∀ g, (((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly =
      (((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))).charpoly.map (iotaOQ N A i) :=
    fun g => Matrix.charpoly_map _ _
  have hle : rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly ≤ R.t := by
    rw [hcpQ, ← hmult x]
    refine (rootMult_le_of_maps (iotaOQ N A i) (iotaOQ_injective N A i)
      (IsLocalRing.residue (N.O i)) _ (Matrix.charpoly_monic _) _).trans (le_of_eq ?_)
    rw [← Matrix.charpoly_map]
    rfl
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hdim : A.lpDim (A.locV i P w) = R.nV := by
    rw [← A.lpDim_tw _ s, ← hP.dim, A.wdOf_dim]
  have hne : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ ≠ 0 := by
    intro σ hσ
    rw [← hine σ hσ]
    exact ((Matrix.charpoly_monic _).map _).ne_zero
  have hleC : rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w)))
      (A.inePol (A.locV i P w) (N.gam0 i w)) ≤ R.t := by
    rw [← hine _ hγ₀I]
    exact (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm.trans_le hle
  obtain ⟨a, b, hab, -, -, -, hb⟩ := hTY.2.1 i P w hS hg htame hleC
  have hdivC : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (X - C (iotaO N A i (chi1 N i σ))) ^ R.t ∣ A.inePol (A.locV i P w) σ := by
    intro σ hσ
    rw [hab, A.inePol_sum, hb σ hσ]
    exact dvd_mul_left _ _
  have hge : R.t ≤ rootMultiplicity (iotaOQ N A i (chi1 N i (N.gam0 i w)))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly := by
    have h1 := (le_rootMultiplicity_iff (hne _ hγ₀I)).mpr (hdivC _ hγ₀I)
    rw [← hine _ hγ₀I] at h1
    exact h1.trans_eq (eq_rootMultiplicity_map (A.iotaQC i).injective _).symm
  have hinj : Function.Injective (Polynomial.map (R := Qbar (N.l i)) (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  have hiO : Function.Injective (iotaO N A i) := fun a b h =>
    iotaOQ_injective N A i ((A.iotaQC i).injective h)
  obtain ⟨χ, hχ⟩ : ∃ χ : G H.E N.Om →* (Qbar (N.l i))ˣ,
      χ = (Units.map (iotaOQ N A i).toMonoidHom).comp (N.chi i 1) := ⟨_, rfl⟩
  have hχv : ∀ g, ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) = iotaOQ N A i (chi1 N i g) := by
    intro g
    rw [hχ]
    rfl
  have hχcont : Continuous fun g => ((χ g : (Qbar (N.l i))ˣ) : Qbar (N.l i)) := by
    simp only [hχv]
    exact (continuous_iotaOQ N A i).comp (N.chi_cont i 1)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have hfo : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), IsOfFinOrder (mapRep (iotaOQ N A i) (r x) σ) := by
    intro σ hσ
    refine finite_zpowers.mp (hfin.subset ?_)
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨σ ^ k, Subgroup.zpow_mem _ hσ k, map_zpow _ σ k⟩
  have hwild : ∀ σ ∈ wildSet N (N.plOm.1 w), σ ∈ Ine (F := H.E) (N.plOm.1 w) ∧
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = (X - 1) ^ R.nV ∧ χ σ = 1 := by
    intro σ hσ
    have hσI : σ ∈ Ine (F := H.E) (N.plOm.1 w) := GlobalTheory.TameEig.wild_mem_Ine (N.plOm.1 w) σ hσ
    have hX : A.inePol (A.locV i P w) σ = (X - 1) ^ R.nV := by
      rw [← A.inePol_tw _ s σ hσI, hP.nice.1 σ hσI hσ, A.lpDim_tw, hdim]
    refine ⟨hσI, ?_, ?_⟩
    · apply hinj
      rw [hine σ hσI, hX]
      simp
    · have h1 := hdivC σ hσI
      rw [hX, show (X - 1 : Polynomial ℂ) = X - C 1 by simp] at h1
      have h2 := (Polynomial.prime_X_sub_C (iotaO N A i (chi1 N i σ))).dvd_of_dvd_pow
        ((dvd_pow_self _ ht0).trans h1)
      have h3 := Polynomial.dvd_iff_isRoot.mp h2
      rw [Polynomial.root_X_sub_C] at h3
      have h4 : chi1 N i σ = 1 := hiO (by rw [← h3, map_one])
      ext
      rw [hχv, h4, map_one]
      rfl
  have hm : rootMultiplicity ((χ (N.gam0 i w) : (Qbar (N.l i))ˣ) : Qbar (N.l i))
      (((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly = R.t := by
    rw [hχv]
    exact le_antisymm hle hge
  obtain ⟨U, U', hUU, hd, hact⟩ := split_tame (Ine (F := H.E) (N.plOm.1 w))
    (wildSet N (N.plOm.1 w)) (N.gam0 i w) hγ₀I htame (mapRep (iotaOQ N A i) (r x)) hcont χ hχcont
    hfo hwild hm
  refine ⟨U, U', hUU, hd, fun γ hγ => ⟨(hact γ hγ).1, fun v hv => ?_⟩⟩
  rw [(hact γ hγ).2 v hv, hχv]

theorem exists_inertia_charpoly_factor_of_tame_type (A : NAut N) (hC : Cheb N) (hr : GoodR N i r) (hT : At.TieGal N A) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k))
    (hL : LGCatN N r A w)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  exact weil_deligne_clause_of_split N r (charpoly_clause_of_chebotarev N hC i r hr) w (iotaOQ N A i) (iotaOQ_injective N A i)
    (exists_isCompl_finrank_inertia_of_charpoly N r A hr hTY w hS hg hL (mult_of_rhobar N r hC hr rb hrb w hw hnr))
    (mult_of_rhobar N r hC hr rb hrb w hw hnr)

theorem SplitI_of_TY (A : NAut N) (hr : GoodR N i r) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (hL : LGCatN N r A w)
    (hty : ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)
    (x : N.X i) : SplitI N r w x := by
  have hcont : Continuous fun g => ((mapRep (iotaOQ N A i) (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
    contQ_of_continuous N A i (r x) (hr x).1
  obtain ⟨P, -, hP0⟩ := hL x
  obtain ⟨s, hP⟩ : ∃ s : ℝ, RelU N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w)
      (A.lpTw (A.locV i P w) s) := ⟨_, hP0⟩
  have hine : ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      (((mapRep (iotaOQ N A i) (r x) σ : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))).charpoly.map (A.iotaQC i).toRingHom =
        A.inePol (A.locV i P w) σ := fun σ hσ =>
    ((A.wdOf_ine i _ w hw hcont σ hσ).trans (hP.ine σ hσ)).trans (A.inePol_tw _ s σ hσ)
  have hfin := (A.wdOf_mono0 i _ w hw hcont).mp hP.mono
  have ht0 : R.t ≠ 0 := fun h => by
    have := R.t_odd
    rw [h] at this
    exact (Nat.not_odd_zero this)
  haveI : CharZero (Kf N i) := ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).charZero
  let ρ : Ine (F := H.E) (N.plOm.1 w) →* GL (Fin (R.r + R.t)) (Kf N i) :=
    (mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp (Ine (F := H.E) (N.plOm.1 w)).subtype
  let χ : Ine (F := H.E) (N.plOm.1 w) →* (Kf N i)ˣ :=
    ((Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)).comp
      (Ine (F := H.E) (N.plOm.1 w)).subtype
  have hrange : (Set.range ρ).Finite := by
    refine Set.Finite.of_finite_image (f := Units.map
      (RingHom.toMonoidHom (RingHom.mapMatrix (m := Fin (R.r + R.t)) (A.iotaQ i)))) ?_ ?_
    · refine hfin.subset ?_
      rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
      exact ⟨γ.1, γ.2, Units.ext rfl⟩
    · intro u _ v _ h
      apply Units.ext
      have h' := congrArg (fun z : GL (Fin (R.r + R.t)) (Qbar (N.l i)) =>
        (z : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l i)))) h
      exact Matrix.map_injective (A.iotaQ i).injective h'
  have hcp : ∀ γ, ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).charpoly =
      (X - 1) ^ R.r * (X - C ((χ γ : (Kf N i)ˣ) : Kf N i)) ^ R.t := by
    intro γ
    apply Polynomial.map_injective ((A.iotaQC i).toRingHom.comp (A.iotaQ i))
      ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).injective
    have hmat : ((ρ γ : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Kf N i)).map (A.iotaQ i) =
        ((mapRep (iotaOQ N A i) (r x) γ.1 : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) :=
      rfl
    rw [← Polynomial.map_map, ← Matrix.charpoly_map, hmat]
    refine (hine γ.1 γ.2).trans ?_
    rw [(hty P).2 γ.1 γ.2]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C]
    rfl
  obtain ⟨Pm, hPm⟩ := split_of_charpoly ht0 ρ χ hrange hcp
  exact ⟨Pm, fun γ hγ => hPm ⟨γ, hγ⟩⟩

end UpperTheory.GalS
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)
open UpperTheory.GalN (SplW)

abbrev RecNotion : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), (IrrGL (k := w.adicCompletion E) → WD h) → Prop

def IsQp {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}

def Tor (y : WD h) : Prop := ∀ s t : ↥(Weil h), LocalGlobalAboveLAlt.Triv y ⁅s, t⁆

def Sqf (y : WD h) : Prop :=
  ∀ γ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A, ((_root_.ReciprocityTheory.Gal.Ine (F := E) A : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ {σ : _root_.Formalism.ConjugateSelfDual.G E Ω | ∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1}) : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) :
        Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) →
    ∀ z : ℂ, 2 ≤ (y.inePol γ).rootMultiplicity z → z ^ (_root_.Formalism.ConjugateSelfDual.normV w - 1) = 1

structure Away (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim

  tor : Tor y → y.mono0 → x = y

  tame0 : IsQp w → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

structure AwayN (x y : WD h) : Prop where
  ine : IsQp w → TmW y → ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g
  spl : IsQp w → TmW y → ∀ (u : WD h) (c : _root_.Formalism.ConjugateSelfDual.G E Ω → ℂ) (t : ℕ), ∀ γ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A,
    ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t → SplW c t (y.lpSum u) → SplW c t (x.lpSum u)
end Local

variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure Above (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
    IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (HT τ)

  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc → ((IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) → (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ IsPstAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ (HT τ)) ∧
    Away (GlobalTheory.Pst.wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) (rc (algNorm σ))

structure Props (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ →
      Away (GlobalTheory.WeilDeligne.wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw), Above Rc π ι r HT P h Bw hj

def TameN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ →
      AwayN (GlobalTheory.WeilDeligne.wdOf h hl ι r) (rc (algNorm σ))

def Row0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), Props Rc π ι r wt HT

end UpperTheory.GalStar
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem inePol_of_unr {y : WD h} (u : y.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : y.inePol σ = (X - 1) ^ y.lpDim := by
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.unr_mk] at u
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, u.2 ⟨σ, hσ⟩, LinearMap.charpoly_one]

theorem NcW.of_unr {y : WD h} (u : y.unr) : NcW y := by
  refine ⟨fun σ hσ => inePol_of_unr u (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), WD.unr_mono0 _ u, fun γ hγ _ z hz => ?_⟩
  rw [inePol_of_unr u hγ] at hz
  have h1 : ((X - 1 : ℂ[X]) ^ y.lpDim).IsRoot z := (rootMultiplicity_pos'.1 (lt_of_lt_of_le (thr_pos w) hz)).2
  have h2 : z - 1 = 0 := by
    simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_one] at h1
    exact pow_eq_zero_iff (by rintro e; rw [e] at h1; simp at h1) |>.1 h1
  rw [sub_eq_zero.1 h2, one_pow]
end

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem nc_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Nc N A y ↔ NcW (T.e w y) := by
  refine and_congr ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩ (and_congr (T.mono0 w y)
    ⟨fun k γ hγ hc z hz => ?_, fun k γ hγ z hz => ?_⟩)
  · have hI := GlobalTheory.TameEig.wild_mem_Ine (E := H.E) _ σ hσ
    rw [← T.inePol w y σ hI, T.dim]
    exact k σ hI hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw
  · exact k γ ⟨hγ, hc⟩ z (by rwa [T.inePol w y γ hγ, ← T.dim])
  · exact k γ hγ.1 hγ.2 z (by rwa [← T.inePol w y γ hγ.1, T.dim])

theorem ncW_of_nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Nc N A y) : NcW (T.e w y) := (nc_iff T y).1 h

theorem relW_of_aw (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Aw (T.e w x) (T.e w y)) : RelW N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], fun u => (T.e w).injective (h.unr ((T.unr w y).1 u)), fun k σ hσ => ?_,
    fun k => (T.mono0 w x).2 (h.mono (ncW_of_nc T k))⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ,
    h.ine (ncW_of_nc T k) _ (deg_ineIncl _)]

theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : UpperTheory.GalN.Ab (T.e w x) (T.e w y)) : UpperTheory.GalN.CuspA N A x y := UpperTheory.GalN.cuspA_of_ab T h1 h

end UpperTheory.GalS
end
end
