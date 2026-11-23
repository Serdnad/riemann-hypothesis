module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle304
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLawG

theorem locTopG_source : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _hsel hL b P hP g z hmid
  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hgC
  refine ⟨⟨g, hgI⟩, rfl, ?_⟩
  intro k hk y y' y'' hy' hky
  obtain ⟨r, hr, hrg, hz⟩ := hmid
  have hred : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (g x) = (redGL _ P.1 k).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [hk]
    exact redV_redGL (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1) hx
  have hmem : redGL _ P.1 k ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H :=
    (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ (redGL _ P.1 k)).2 ⟨g, hgC, hred⟩
  set c : X.Kˣ := (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨redGL _ P.1 k, hmem⟩ with hcdef
  have hcz : (c : X.K) = z := by
    rw [hz]
    exact hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨redGL _ P.1 k, hmem⟩ g r hr hrg hred
  have hlev : GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k c :=
    ⟨fun _ => ⟨hmem, rfl⟩, fun _ h => absurd hP h⟩
  have hrho : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    refine unitV_congr _ ?_
    rw [(det_glint k).2, ← redGL_val, hk, redGL_val]
    exact (det_glint (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1)).2
  rw [hrho, ← hcz]
  have hm := hL.hm
  have key := GlobalTheory.TopLaw.locTop_source hX hPr hL hlev
  clear_value c
  clear hcdef hcz hrho hred hz hrg hr hmem
  revert key y
  cases R with
  | mk e k0 m t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    change m = m2 + 2 at hm
    subst hm
    intro y key
    have := key y (fun _ => hy') (fun h => absurd hP h) (fun _ => hky) (fun h => absurd hP h)
    unfold locTop at this
    rw [PhiTopG_eq]
    exact this

end GlobalTheory.TopLawG
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published GlobalTheory.ContraPair

namespace GlobalTheory.GalCut

theorem clauseAt_of_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous r → UpperTheory.V.Af.RepIso r r' → ∀ c w, ClauseAt c π ι r w → ClauseAt c π ι r' w := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' _ hiso c w hc
  obtain ⟨p, hp⟩ := hiso
  have hcw : ∀ {A : ValuationSubring Ω} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (g : Weil h), p * r g = r' g * p :=
    fun h g => by rw [hp]; group
  have hcd : ∀ (A : ValuationSubring Ω) (g : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A)), r'.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype g =
      p * r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype g * p⁻¹ := fun A g => hp g
  cases c with
  | ss =>
    intro hl A h rc hrc σ hσ g
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h rc hrc σ hσ g
  | pure =>
    intro hl A h wt hwt
    rw [← wdOf_eq_of_conj hl p (hcw h)]
    exact hc hl A h wt hwt
  | dR =>
    intro P AI hT A hA O _ _ _ Bw hj
    obtain ⟨h1, h2⟩ := hc P AI hT A hA O Bw hj
    obtain ⟨k1, -, -, k4⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact ⟨k1 h1, fun τ LL' τ' hτ J hJ => k4 τ J (h2 τ LL' τ' hτ J hJ)⟩
  | crys =>
    intro P AI hT A hA O _ _ _ Bw hj σ hσ hS
    obtain ⟨-, k2, -, -⟩ := GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw a _ _ p (hcd A)
    exact k2 (hc P AI hT A hA O Bw hj σ hσ hS)
  | iwa =>
    intro P AI hT A h O _ _ _ Bw hj σ hσ hI
    obtain ⟨h3, h4⟩ := hc P AI hT A h O Bw hj σ hσ hI
    exact ⟨GlobalTheory.AboveL.RepConj.isSstAt_conj P Bw p (hcd A) h3, fun rc hrc =>
      (GlobalTheory.AboveL.RepConj.wdAt_conj P ι Bw h hj p (hcd A)).trans (h4 rc hrc)⟩

end GlobalTheory.GalCut
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem exists_place_dvd_prime {K : Type} [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
      simp [this])
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((l : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    have : ((l : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hmem⟩

theorem continuous_tw_of_continuous {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {μ : Γ →* kˣ} (hr : Continuous r) (hμ : Continuous μ) :
    Continuous (UpperTheory.V.Af.tw r μ) := by
  have h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  simp only [← map_inv]
  exact h1.comp continuous_inv

theorem ex_good_of_ex_csd : AutomorphicFormsFiniteGL → Ex .csd → Ex .good := by
  intro hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs
  obtain ⟨w₀, hw₀⟩ := exists_place_dvd_prime (K := E) l
  have hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀ := by
    by_contra h
    exact (hs.2.2.2.2 w₀ h).1 hw₀
  obtain ⟨κ, m, hκ, -, hs'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hA E l a ha π χ hs w₀ hsplit
  obtain ⟨r', hr'c, hr'⟩ := hcsd E Ω l ι a ha (π.twist κ) _ hs'
  have hκi : (κ⁻¹).IsAlg (-m) := fun k => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨art, hart, hμ⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)
  refine ⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩
  have h := UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ
  rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GalCut
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CrysTwistBack

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {a : ℕ}

theorem isCrysAt_of_tw {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (h : IsCrysAt P Bw (UpperTheory.V.Af.tw r c))
    (hc : IsCrysAt P Bw (GlobalTheory.TripleGal.rk1 c)) : IsCrysAt P Bw r := by
  obtain ⟨L₁, r₁, m₁, hr₁⟩ := h
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  have hp := (local_ext P Bw l₁ r₁).1.2 hr₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    simp [GlobalTheory.TripleGal.rk1]
  have hM : IsModel Bw r L (UpperTheory.V.Af.tw r₁' d⁻¹) := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        ((UpperTheory.V.Af.tw r c g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((UpperTheory.V.Af.tw r₁' d⁻¹ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul, map_mul, e, UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      show algebraMap ↥L.1 (Om l) (d g : ↥L.1) = (c g : Om l) from hcd g, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨L, _, hM, ?_⟩
  let θ : ↥(GK Bw.Kw) →* (↥L.1)ˣ := d.comp Bw.e.symm.toMonoidHom
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T Bw.Kw L (Bw.repE L (UpperTheory.V.Af.tw r₁' d⁻¹)) (Bw.repE L r₁') θ
    (fun g x => ?_) ?_).2 hp
  · rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul]
    change _ = ((d (Bw.e.symm g) : ↥L.1) * ((d⁻¹ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)) • _
    rw [MonoidHom.inv_apply, Units.mul_inv, one_smul]
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) hq
    change (Bw.repE L c₂' g x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm g))

end GlobalTheory.CrysTwistBack

namespace GlobalTheory.CrysTwistBack

theorem isSpherical_twist_of_unr {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (κ : HChar E) (hκ : κ.UnrAt w)
    (h : GlobalTheory.SmGL.IsSpherical σ.ρ) :
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have hg : g.1 ∈ GlobalTheory.LFun.KGL w (n := a) := hK ▸ g.2
  have h1 : CuspSub.locDet a κ w g.1 = 1 := hκ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)
  have h3 := hv g
  show ((CuspSub.locDet a κ w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

theorem holds_good_crys : AutomorphicFormsFiniteGL → HeckeLAdicCharacterAbove → Holds .csd .crys → Holds .good .crys := by
  intro hF hA hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  obtain ⟨κ, m, hκ, hκu, hcs⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hch⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hch l ι κ m (fun k _ => hκ k)
  have hw' : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ hr.1 hμc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have h1 := hC E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hcs (UpperTheory.V.Af.tw r μ) hw' w hw P AI hT A hAw O Bw hj _
    (hσ.twist κ) (isSpherical_twist_of_unr a w σ κ hκu hsph)
  have h2 := (hA E Ω l P AI hT ι art hart κ m μ (fun k _ => hκ k) hμc hμ w A hAw O Bw hj).2.2.1 hκu
  obtain ⟨T⟩ := hT
  exact isCrysAt_of_tw T Bw (μ.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) h1 h2

end GlobalTheory.CrysTwistBack

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.ZeroChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem latAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) :
    I.latAt u a 0 (I.eCls0 l u a c) = I.latAt u I.mu0 0 c := by
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  unfold TC.latAt
  rw [dite_eq_left (Nat.zero_le _), dite_eq_left (Nat.zero_le _), e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem range_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl)
    (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) (I.eCls0 l u a c)).range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) c).range := by
  rw [Chart0.stab_range0 I hI, Chart0.stab_range0 I hI]
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  rw [e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem map_conj_mul {G : Type} [Group G] (U : Subgroup G) (y k : G) (hk : k ∈ U) :
    U.map (MulAut.conj (y * k)).toMonoidHom = U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, hg⟩
    refine ⟨k * x * k⁻¹, (conj_mem_iff hk x).2 hx, Eq.trans ?_ hg⟩
    show y * (k * x * k⁻¹) * y⁻¹ = y * k * x * (y * k)⁻¹
    group
  · rintro ⟨x, hx, hg⟩
    refine ⟨k⁻¹ * x * k, by simpa using (conj_mem_iff (inv_mem hk) x).2 hx, Eq.trans ?_ hg⟩
    show y * k * (k⁻¹ * x * k) * (y * k)⁻¹ = y * x * y⁻¹
    group

end GlobalTheory.TwU.AtTrue.ZeroChart

end

namespace GlobalTheory.TwU.AtTrue.ZeroChart

open scoped TensorProduct



theorem chart_of_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  intro B X I hI hP l Z u a Q K κ hK
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  let e := I.eCls0 l u a
  have hU : ∀ c, (κ c).1 ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ((K.lev.U_eq _).1 (κ c).2).1
  let κU : ∀ c, UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ⟨(κ c).1, hU c⟩
  have hL : ∀ c, (κ c).1 ∈ levelAfL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) K.lev.Lb := fun c =>
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ _ _ _ _ K.lev.Lb_fin _).2
      ⟨hU c, fun v => K.lev.Uloc_lev v (((K.lev.U_eq _).1 (κ c).2).2 v)⟩
  have hlat : ∀ c'', I.latAt u a 0 c'' = I.latAt u I.mu0 0 (e.symm c'') := by
    intro c''
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact latAt_eCls0 I hI l u a c
  have hrng : ∀ c'' (γ : GL (Fin (B.R.N 0)) B.host.E),
      γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'').range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) (e.symm c'')).range := by
    intro c'' γ
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact range_eCls0 I hI l u a c γ
  have hmem : ∀ c'' (s : (I.stp u a 0).Stab c''),
      MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'' s ∈
        UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi) := by
    intro c'' s
    obtain ⟨t, ht⟩ := (hrng c'' _).1 ⟨s, rfl⟩
    rw [← ht]
    exact (congrArg (fun g => g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi))
      (hK (e.symm c'') t)).mp (K.stabI (e.symm c'') t).2
  have hcls : ∀ c, (Quotient.mk'' (K.y c * κU c) : Cls K.lev) = Quotient.mk'' (K.y c) := fun c => by
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨1, one_mem _, (κU c)⁻¹, ?_, by group⟩
    exact inv_mem (κ c).2
  refine ⟨fun _ =>
    { lev :=
        { K.lev with
          Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (Or.inl h)) hT
          chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (Or.inl hv)) }
      y := fun c' => K.y (e.symm c'.1) * κU (e.symm c'.1)
      y_bij := ?_
      y_lat := ?_
      stabI := fun c' => (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)
      stabI_inj := fun c' s t h => MemChart.stM_inj (Chart0.lvG I a) (Chart0.lvQ I a) _ _ ((l.ch u a).step 0) c'.1 (congrArg Subtype.val h)
      stabI_range := ?_ }, rfl, rfl, rfl, fun x x' h => ?_, fun c => ?_, fun c s => rfl⟩
  · convert K.y_bij.comp (e.symm.bijective.comp
        (Equiv.subtypeUnivEquiv (p := fun c' : (I.stp u a 0).Cl => (fun _ => ()) c' = ()) (fun _ => rfl)).bijective) using 1
    funext c'
    exact hcls (e.symm c'.1)
  · intro c' x
    rw [hlat c'.1]
    refine (K.y_lat (e.symm c'.1) x).trans ?_
    show _ ↔ ((((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)⁻¹).1 *ᵥ x ∈ _)
    have hm : ∀ (g h : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0)) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)),
        ((g * h)⁻¹).1 *ᵥ x = (h⁻¹).1 *ᵥ ((g⁻¹).1 *ᵥ x) := by
      intro g h
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    rw [hm (K.y (e.symm c'.1)).1 (κ (e.symm c'.1)).1]
    exact (inv_mem (hL _)).2 _
  · intro c' γ
    have h1 : γ ∈ ((MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)).range ↔
        γ.1 ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).range :=
      ⟨fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩, fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩⟩
    refine h1.trans ((hrng c'.1 γ.1).trans (Iff.trans ?_ ((K.stabI_range (e.symm c'.1) γ).trans ?_)))
    · exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ((hK _ t).trans ht)⟩, fun ⟨t, ht⟩ => ⟨t, (hK _ t).symm.trans (congrArg Subtype.val ht)⟩⟩
    show _ ↔ _ ∈ K.lev.U.map (MulAut.conj ((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)).toMonoidHom
    rw [map_conj_mul _ _ _ (κ _).2]
  · show K.lev.chi x = K.lev.chi x'
    exact congrArg K.lev.chi (Subtype.ext h)
  · show (K.y (e.symm (e c))).1 * (κ (e.symm (e c))).1 = _
    rw [e.symm_apply_apply]

end GlobalTheory.TwU.AtTrue.ZeroChart
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), ∃ eM : ((I.rec7 l Z).div.Nu u).V ≃+ Formalism.L2.Col.MramV (Pr := B.primes X) B.wts I.Ch u, (∀ (r : (I.rec7 l Z).what₂.LL) x, eM (r • x) = (show B.fields.K from r) • eM x) ∧ (∀ x, x ∈ DV.MramL (I.rec7 l Z) u ↔ eM x ∈ Formalism.L2.Col.MramL (Pr := B.primes X) B.wts I.Ch u) ∧ (∀ x, (I.rec7 l Z).nuIn u x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 (eM x).1) ∧ ∀ a φ, (I.fm l u a).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (GlobalTheory.Mem.Col2.KerRat.colForm I l h u I.mu0 φ)) := by
  first | exact @GlobalTheory.AtG.ramCols_true | exact GlobalTheory.AtG.ramCols_true | (intros; apply GlobalTheory.AtG.ramCols_true <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | exact GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | (intros; apply GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_doubleCosetCommuting_map_principalCongruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  first | exact @GlobalTheory.HeckeIsoMap.isoMap | exact GlobalTheory.HeckeIsoMap.isoMap | (intros; apply GlobalTheory.HeckeIsoMap.isoMap <;> assumption)
end
