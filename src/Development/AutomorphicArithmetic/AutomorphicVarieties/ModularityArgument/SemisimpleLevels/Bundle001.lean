module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.AbW
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem teich_not_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l N : ℕ} (h : l.Coprime N)
    (hl : A.valuation (l : Ω) < 1) : ¬ A.valuation (N : Ω) < 1 := by
  intro hN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have ha : A.valuation (a : Ω) ≤ 1 := by simpa using A.valuation_le_one (a : A)
  have hb : A.valuation (b : Ω) ≤ 1 := by simpa using A.valuation_le_one (b : A)
  have hv : A.valuation ((a : Ω) * l + (b : Ω) * N) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) hl
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) hN
  have h1 : ((a : Ω) * l + (b : Ω) * N) = 1 := by
    have e := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at e
    exact e
  rw [h1, map_one] at hv
  exact lt_irrefl _ hv

theorem UpperTheory.V.Lev.teichDvd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.om → l ∣ N := by
  intro Ω _ _ _ l _ c D hD N hN hK
  by_contra hnd
  have hp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have hl := hD.pl_over l hp
  have hNA := teich_not_lt (D.pl l) hcop hl
  have hNz : NeZero N := ⟨by omega⟩
  have hIne := (Chr.clsFacts ℚ Ω N).2.2.2.2 (D.pl l) hNA
  obtain ⟨σ, hσ, hcyc⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l (D.pl l) hl (-1)
  have hom : D.om σ = 1 := by
    apply hK σ
    intro ζ hζ
    rw [Chr.cls_spec N σ ζ hζ, MonoidHom.mem_ker.mp (hIne hσ), Units.val_one, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · have h1 : N = 1 := by omega
      subst h1
      simp at hζ ⊢
      exact hζ.symm
    · rw [Nat.one_mod_eq_one.mpr (by omega), pow_one]
  have hbar := hD.om_bar σ
  simp only [Raw.bar, hom, chiO, MonoidHom.comp_apply, hcyc] at hbar
  simp [Units.coe_map] at hbar
  have hch := (Ws.Gys.coefFacts c (ResidueField c.O) (residue c.O)
    (fun x hx => (IsLocalRing.residue_eq_zero_iff x).mpr hx)).1
  have h2 : ((2 : ℕ) : ResidueField c.O) = 0 := by
    have e : (1 : ResidueField c.O) + 1 = 0 := by
      nth_rewrite 1 [hbar]
      exact neg_add_cancel 1
    rw [Nat.cast_ofNat, ← e]
    norm_num
  have hdvd := (CharP.cast_eq_zero_iff (ResidueField c.O) l 2).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hge := hp.two_le
  exact hD.l_odd (by omega)
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

def SsCmp {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v} (x y : WD h) : Prop :=
  AbW x ∨ AbW y → ∀ s, x.charPol s = y.charPol s

theorem SsCmp.of_eq {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v} {x y : WD h} (e : x = y) : SsCmp x y := fun _ _ => by rw [e]

def SsCalc : Prop :=
  ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v),
    (∀ (n : ℕ) (x : WD h) (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) → AbW x) ∧
    (∀ x x' y y' : WD h, SsCmp x y → SsCmp x' y' → SsCmp (x.lpSum x') (y.lpSum y')) ∧
    ∀ x y z : WD h, z.lpDim = 1 → (SsCmp (x.lpChar z) (y.lpChar z) ↔ SsCmp x y)

def SsMove : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (x y : WD h) (x' y' : WD h'),
      WDRel (RingEquiv.refl Ω) x x' → WDRel (RingEquiv.refl Ω) y y' → SsCmp x' y' → SsCmp x y

abbrev WO {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w} (ι : Qbar l ≃+* ℂ)
    (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l)) (y : WD h) : Prop := IsWDOf ι r y

def CsdSs : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, GlobalTheory.ContraPair.DualIsConj π → GKCoh.IsCohomological π →
    ∃ R : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous R ∧ IsSSRep R ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
        (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WO ι R (rc (algNorm σ))) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
          (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (R.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
            SsCmp (wdAt P ι Bw h hj (R.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) (rc (algNorm σ))

theorem csdSs_of_full (H : GlobalTheory.Published.CaraianiLocalGlobalDual) : CsdSs := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hd hc
  obtain ⟨R, h1, h2, h3, h4⟩ := H E Ω l ι a ha π hd hc
  refine ⟨R, h1, h2, h3, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  exact ⟨(h4 P AI hT w A h O Bw hj).1, fun σ hσ rc hrc => SsCmp.of_eq ((h4 P AI hT w A h O Bw hj).2 σ hσ rc hrc)⟩

end UpperTheory.V.Lev

end
end
