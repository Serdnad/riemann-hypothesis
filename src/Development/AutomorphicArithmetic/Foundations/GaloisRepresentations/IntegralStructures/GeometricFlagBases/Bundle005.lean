module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem aeval_smul_prod {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (S : Multiset K) :
    aeval (c • M) ((S.map fun b => X - C (b * c)).prod) =
      c ^ Multiset.card S • aeval M ((S.map fun b => X - C b).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]
    simp only [map_sub, aeval_X, aeval_C]
    have e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    rw [e, ← smul_sub, smul_mul_smul_comm, pow_succ']

theorem UpperTheory.Gal.Int.Geo.twES :
    UpperTheory.Gal.Int.Geo.TwES := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA
  have hχ := hCl.1 hw A hA
  obtain ⟨hi, hf⟩ := hES A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 := (hχ.1 s hs)
    have h2 : (χ s : Qbar l) = 1 := by
      have h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l) := by
        simp [GlobalTheory.TripleGal.rk1]
      rw [h1] at h3
      simpa using h3.symm
    apply Units.ext
    rw [UpperTheory.V.Af.tw_val, hi s hs, h2]
    simp
  · have hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c := by
      have h1 := (hχ.2 σ hσ)
      have h2 := (UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹
      simp only [UpperTheory.Gal.TP.Sub.cp] at h2
      rw [h2] at h1
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] at h1
      exact C_injective (sub_right_injective h1)
    have hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom =
        ((T.map ι.symm).map fun b => X - C b).prod := by
      intro T
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
      simp
    have hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← hk]; simp
    have hfin := hf σ hσ
    rw [hs] at hfin
    have hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)) := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [map_mul, hc]
    rw [UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]
    have := aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)
    rw [hfin, smul_zero] at this
    exact this
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo

structure Steps : Prop where
  rep : RepEx
  es : ESStep
  crys : CrysStep
  jump : JumpStep
  phi : PhiStep
  cut : CutStep
  twES : TwES
  twCrys : TwCrys
  twJ : TwJ
  twPhi : TwPhi
  phiOf : PhiOf
  card : SatCard
  jumpsOf : JumpsOf
  rich : RichOf
  char : TP.Sub.CharEx
  ss : TP.Sub.SSLeft
  cont : TP.Sub.ContLeft

theorem map_inv_mul (R : Multiset ℂ) (c : ℂˣ) : (R.map (· * ((c : ℂ))⁻¹)).map (· * (c : ℂ)) = R := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id R]
  exact Multiset.map_congr rfl fun x _ => by simp

theorem Pack.rep (h : Steps) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a d : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (P : Pack ι d U)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (hlac : LacWtAt ι v U) (hP : P.HTFor v) :
    ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w → CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧
      ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → PhiKilled ι ρ w a B := by
  obtain ⟨dd, ρ, hc, hs, hp⟩ := h.rep E Ω l P.H P.θ P.nice
  obtain ⟨L, hL, -⟩ := h.char E Ω l ι
  obtain ⟨hχ, hcl⟩ := hL P.κ P.m P.alg
  have hES : ∀ w B, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → CongFor ι a P.H P.θ P.κ w B →
      ESAt ι (tw ρ (L P.κ P.m)) w (algSat a (normV w) B) := by
    rintro w B hw ⟨hu, ϑ, h1, h2⟩
    have := h.twES E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) hw _
      (h.es E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rwa [map_inv_mul] at this
  have hHT : ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w →
      CrysAt (tw ρ (L P.κ P.m)) w ∧ JumpsOcc U ι (tw ρ (L P.κ P.m)) w := by
    rintro w hw ⟨hu, h1, h2⟩
    have hg := (h.cut E _ P.H P.θ P.nice w).1 h1
    have h3 : ∀ τ : E →+* ℂ, ∃ σ : ℂ ≃+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam,
        HodgeAt (ι.trans σ) P.H P.θ (σ.toRingHom.comp τ) (j + P.m τ) := fun τ => by
      by_cases hτ : OverPl ι τ w
      · obtain ⟨σ, hσ⟩ := h2 τ hτ
        exact ⟨σ, fun _ => hσ⟩
      · exact ⟨RingEquiv.refl ℂ, fun h' => absurd h' hτ⟩
    choose σ hσ using h3
    have hJ : JOcc ι ρ w fun τ j => HodgeAt (ι.trans (σ τ)) P.H P.θ ((σ τ).toRingHom.comp τ) j := by
      intro Q AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
      exact h.jump E Ω l (ι.trans (σ (ι.toRingHom.comp τ))) P.H P.θ P.nice dd ρ hc hp w hw hg Q AI hT A hA O Bw hj τ LL' τ' hi
    refine ⟨?_, h.jumpsOf E Ω l ι a dd U _ w _ ?_ (h.twJ E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _ hJ)⟩
    · obtain ⟨C, hC, -⟩ := hg
      exact h.twCrys E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) (h.crys E Ω l P.H P.θ P.nice dd ρ hc hp w hw C hC)
    · intro τ hτ lam hl j hj
      simpa only [sub_neg_eq_add] using hσ τ hτ lam hl j hj
  refine ⟨dd, tw ρ (L P.κ P.m), ⟨(h.cont _ _ dd 0).2.2.1 ρ _ hc hχ, (h.ss _ _ dd 0).2.2 ρ _ hs, ?_,
    h.rich E Ω l ι a dd U _ v hv hlac (hHT v hv hP).2⟩, fun w hw hC B hB => hES w B hw (hC B hB), hHT, ?_⟩
  · obtain ⟨X, hX⟩ := P.cong
    exact ⟨X, fun w h1 h2 h3 B hB => hES w B h3 (hX w h1 h2 h3 B hB)⟩
  · intro w hw hC B hB
    obtain ⟨hu, ϑ, h1, h2⟩ := hC B hB
    have := h.twPhi E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _
      (h.phi E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rw [map_inv_mul] at this
    exact h.phiOf E Ω l ι dd _ w a B (h.card E a U w B hB) this

theorem geoOne_of (h : Steps) (hP : PackEx) : GeoOne := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph hlac
  obtain ⟨⟨P, hP0⟩, hA, hB⟩ := hP E l ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  refine ⟨?_, fun w hw hl hs => ?_, fun w hl hk ha0 hav hs => ?_⟩
  · obtain ⟨dd, ρ, hV, -⟩ := P.rep h Ω hv hlac hP0
    exact ⟨dd, ρ, hV⟩
  · obtain ⟨P, h1, h2⟩ := hA w hw hl hs
    obtain ⟨dd, ρ, hV, hE, -⟩ := P.rep h Ω hv hlac h1
    exact ⟨dd, ρ, hV, hE w hl h2⟩
  · obtain ⟨⟨P, h1, h2⟩, P', h1', h2'⟩ := hB w hl hk ha0 hav hs
    obtain ⟨dd, ρ, hV, -, hC, -⟩ := P.rep h Ω hv hlac h1
    obtain ⟨dd', ρ', hV', -, -, hF⟩ := P'.rep h Ω hv hlac h1'
    exact ⟨⟨dd, ρ, hV, hC w hl h2⟩, dd', ρ', hV', hF w hl h2'⟩

end UpperTheory.Gal.Int.Geo

end
end
