module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle909
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import GroundTheory.AutomorphicForms.Bundle009
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.AbsIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.AutomorphicForms.SmoothRep

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm

private theorem locP_of (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) : Pa.LocP :=
  ⟨GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.loc.llc P.loc.conv P.loc.dzc P.loc.dzi P.loc.brauer P.loc.chev P.aut.art
               P.loc.exh P.loc.multi P.loc.cos P.loc.zel P.loc.geo P.loc.bz,
    P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩

private theorem rad_of_dense {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
    (J : Ideal B.B) (h : B.Dense J) : J.IsRadical := by
  rintro b ⟨k, hk⟩
  refine h (fun _ j _ => ((j : ℕ) : ℤ)) (fun _ _ i j hij => Int.ofNat_lt.2 hij) b fun x hx _ => ?_
  have h1 : x (b ^ k) = 0 := hx hk
  rw [map_pow] at h1
  exact IsReduced.eq_zero _ ⟨k, h1⟩

private theorem cohP_of (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace UpperTheory.V.Z.J.D

section Abs

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

private def mulMap (P K : Subgroup G) (hK : IsOpen (K : Set G)) (σ σ' : Representation ℂ P W) (c : G → ℂˣ)
    (hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v))
    (hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x) : smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P σ') where
  toFun f := ⟨⟨fun x => ((c x : ℂˣ) : ℂ) • f.1.1 x, fun p x => by
      have h := f.1.2 p x
      show ((c ((p : G) * x) : ℂˣ) : ℂ) • f.1.1 ((p : G) * x) = _
      rw [h]
      exact hl p x _⟩, by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (Filter.inter_mem (f.2.mem_nhds (by simp)) (hK.mem_nhds K.one_mem)) ?_)
      rintro g ⟨h1, h2⟩
      have h3 : ind P σ g f.1 = f.1 := h1
      refine Subtype.ext (funext fun x => ?_)
      have h4 : f.1.1 (x * g) = f.1.1 x := congrArg (fun φ : indSpace P σ => φ.1 x) h3
      show ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c x : ℂˣ) : ℂ) • f.1.1 x
      rw [h4, hr g h2]⟩
  map_add' f f' := Subtype.ext (Subtype.ext (funext fun x => smul_add _ (f.1.1 x) (f'.1.1 x)))
  map_smul' a f := Subtype.ext (Subtype.ext (funext fun x => smul_comm _ a (f.1.1 x)))

private theorem equiv_of_char (P K : Subgroup G) (hK : IsOpen (K : Set G))
    (hPK : ∀ x : G, ∃ p : P, ∃ w ∈ K, x = (p : G) * w) (σ σ' : Representation ℂ P W) (R : P →* ℂˣ)
    (hR : ∀ p : P, (p : G) ∈ K → R p = 1) (hσ : ∀ (p : P) (v : W), σ' p v = ((R p : ℂˣ) : ℂ) • σ p v) :
    Nonempty (Representation.Equiv ((smInd P σ).comp K.subtype) ((smInd P σ').comp K.subtype)) := by
  obtain ⟨c, hc⟩ : ∃ c : G → ℂˣ, ∀ (p : P) (w : G), w ∈ K → c ((p : G) * w) = R p := by
    refine ⟨fun x => R (Classical.choose (hPK x)), fun p w hw => ?_⟩
    obtain ⟨w', hw', hx⟩ := Classical.choose_spec (hPK ((p : G) * w))
    set q := Classical.choose (hPK ((p : G) * w))
    have hqp : ((q⁻¹ * p : P) : G) ∈ K := by
      have : ((q⁻¹ * p : P) : G) = w' * w⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hx, mul_inv_cancel_right]
      rw [this]
      exact K.mul_mem hw' (K.inv_mem hw)
    have := hR _ hqp
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x := by
    intro κ hκ x
    obtain ⟨p, w, hw, rfl⟩ := hPK x
    rw [mul_assoc, hc _ _ (K.mul_mem hw hκ), hc _ _ hw]
  have hmul : ∀ (p : P) (x : G), c ((p : G) * x) = R p * c x := by
    intro p x
    obtain ⟨q, w, hw, rfl⟩ := hPK x
    rw [← mul_assoc, ← Subgroup.coe_mul, hc _ _ hw, hc _ _ hw, map_mul]
  have hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v) := by
    intro p x v
    rw [hσ, map_smul, smul_smul, hmul, Units.val_mul]
  have hl' : ∀ (p : P) (x : G) (v : W),
      ((((fun y => (c y)⁻¹) ((p : G) * x)) : ℂˣ) : ℂ) • σ' p v = σ p ((((fun y => (c y)⁻¹) x : ℂˣ) : ℂ) • v) := by
    intro p x v
    simp only [hσ, map_smul, smul_smul, hmul, ← Units.val_mul]
    congr 2
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hr' : ∀ κ ∈ K, ∀ x, (fun y => (c y)⁻¹) (x * κ) = (fun y => (c y)⁻¹) x := by
    intro κ hκ x
    simp only [hr κ hκ x]
  refine ⟨{ toFun := mulMap P K hK σ σ' c hl hr
            map_add' := (mulMap P K hK σ σ' c hl hr).map_add
            map_smul' := (mulMap P K hK σ σ' c hl hr).map_smul
            isIntertwining' := ?_
            invFun := mulMap P K hK σ' σ (fun y => (c y)⁻¹) hl' hr'
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro g
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g)
    rw [hr g g.2]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (((c x)⁻¹ : ℂˣ) : ℂ) • (((c x : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • ((((c x)⁻¹ : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Abs

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_pw (x : GL (Fin n) k) :
    ∃ p : parab k (points (Fin n)), ∃ w ∈ KO k (Fin n), x = (p : GL (Fin n) k) * w := by
  obtain ⟨u, g, w, hw, hx⟩ := UnitInd.exists_iwasawa (points (Fin n)) x
  refine ⟨⟨(u : GL (Fin n) k) * leviEmb k (points (Fin n)) g,
    mul_mem (unipRad_le_parab k (points (Fin n)) u.2) (leviEmb_mem_parab k (points (Fin n)) g)⟩, w, hw, hx⟩

open GlobalTheory.SmGL.PrinProd in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
private theorem dg_mem_Uo (p : parab k (points (Fin n))) (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (i : Fin n) :
    dg p i ∈ UpperTheory.V.Hi.Uo k := by
  have h1 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).1 i i
  have h2 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).2 i i
  rw [← PrinProd.val_dg] at h1
  have h3 : ((dg p⁻¹ i : kˣ) : k) ∈ 𝒪[k] := by
    rw [PrinProd.val_dg]
    simpa using h2
  rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val] at h3
  change valuation k _ = 1
  have a1 : valuation k ((dg p i : kˣ) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 h1
  have a2 : valuation k ((dg p i : kˣ) : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).1 h3
  rw [map_inv₀] at a2
  have hne : valuation k ((dg p i : kˣ) : k) ≠ 0 := by simp
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 a2)

open GlobalTheory.SmGL.PrinProd in
private theorem sB_apply (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) (v : ℂ) :
    sB χ p v = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂˣ) : ℂ) *
      (((torusChar χ (dg p) : ℂˣ) : ℂ) * v) := rfl

end Loc


open GlobalTheory.SmGL.PrinProd in
theorem psRes : PsRes := by
  intro k _ _ _ _ n ω ω' _ _ h
  let χ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k ((↑n - 1) / 2)
  let χ' : Fin n → kˣ →* ℂˣ := fun i => ω' i * absPow k ((↑n - 1) / 2)
  let ρ : Fin n → kˣ →* ℂˣ := fun i => ω' i * (ω i)⁻¹
  have hχ : ∀ t, torusChar χ' t = torusChar ρ t * torusChar χ t := by
    intro t
    simp only [torusChar_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [χ, χ', ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  refine equiv_of_char (parab k (points (Fin n))) (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO exists_pw
    (sB χ) (sB χ') ((torusChar ρ).comp dg) (fun p hp => ?_) (fun p v => ?_)
  · rw [MonoidHom.comp_apply, torusChar_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← h i ⟨_, dg_mem_Uo p hp i⟩, mul_inv_cancel]
  · rw [sB_apply, sB_apply, smul_eq_mul, MonoidHom.comp_apply, hχ, Units.val_mul]
    ring

end UpperTheory.V.Z.J.D
end
end

section

open UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.schurGL :
    SchurGL := by
  intro L _ _ n w τ
  letI := τ.acg
  letI := τ.mod
  haveI : τ.ρ.IsIrreducible := τ.irred
  have hsm : GroundTheory.Automorphic.IsSmooth τ.ρ := τ.smooth
  refine ⟨τ.irred, fun f hf => ?_⟩
  let φ : Representation.IntertwiningMap τ.ρ τ.ρ :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext fun v => hf g v }
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, LinearMap.ext fun v => (congrArg (fun h : Representation.IntertwiningMap τ.ρ τ.ρ => h v) hc).symm⟩
end

section

open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section SlopeTestRemainingChoices

variable {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private lemma stable_eq {τ : Representation ℂ G W'} (hτ : τ.IsIrreducible) (P : Submodule ℂ W')
    (hP : ∀ g, ∀ v ∈ P, τ g v ∈ P) : P = ⊥ ∨ P = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  rcases eq_bot_or_eq_top (⟨P, fun g _ hv => hP g _ hv⟩ : Subrepresentation τ) with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing in
private lemma indep_fin {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    ∀ (n : ℕ) (b : Fin n → (W' →ₗ[ℂ] W)), (∀ i, Intw τ ρ (b i)) → LinearIndependent ℂ b →
      ∀ u : Fin n → W', ∑ i, b i (u i) = 0 → u = 0 := by
  intro n
  induction n with
  | zero => intro b _ _ u _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro b hb hli u hu
    have hli' : LinearIndependent ℂ fun i : Fin n => b i.succ :=
      hli.comp _ (Fin.succ_injective n)
    have ih' := ih (fun i => b i.succ) (fun i => hb i.succ) hli'
    let A : (Fin n → W') →ₗ[ℂ] W := ∑ i, (b i.succ) ∘ₗ LinearMap.proj i
    have hA : ∀ v, A v = ∑ i, b i.succ (v i) := fun v => by simp [A, LinearMap.sum_apply]
    have hAinj : Function.Injective A := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact ih' v (by rw [← hA]; exact hv)
    have hAeq : ∀ g v, A (fun i => τ g (v i)) = ρ g (A v) := fun g v => by

      rw [hA, hA, map_sum]
      exact Finset.sum_congr rfl fun i _ => hb i.succ g (v i)
    have hsum : b 0 (u 0) + A (fun i => u i.succ) = 0 := by
      rw [hA, ← hu, Fin.sum_univ_succ]
    let P : Submodule ℂ W' := (LinearMap.range A).comap (b 0)
    have hP : ∀ g, ∀ v ∈ P, τ g v ∈ P := by
      rintro g v ⟨y, hy⟩
      refine ⟨fun i => τ g (y i), ?_⟩
      rw [hAeq, hy]
      exact (hb 0 g v).symm
    rcases stable_eq hτ.1 P hP with h | h
    · have h0 : u 0 = 0 := by
        have : u 0 ∈ P := ⟨-fun i => u i.succ, by
          rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hsum |>.symm ▸ rfl)⟩
        rw [h] at this
        simpa using this
      have h1 : (fun i : Fin n => u i.succ) = 0 := by
        apply ih'
        rw [← hA, ← hsum, h0]
        simp
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun h1 j
    · exfalso
      have hall : ∀ v, ∃ y, A y = b 0 v := fun v => by
        have : v ∈ P := h ▸ Submodule.mem_top
        exact this
      choose T hT using hall
      have hTadd : ∀ v v', T (v + v') = T v + T v' := fun v v' =>
        hAinj (by rw [map_add (f := _), hT, hT, hT, map_add (f := _)])
      have hTsmul : ∀ (a : ℂ) v, T (a • v) = a • T v := fun a v =>
        hAinj (by rw [map_smul, hT, hT, map_smul])
      have hTg : ∀ g v i, T (τ g v) i = τ g (T v i) := fun g v i => by
        have : T (τ g v) = fun i => τ g (T v i) :=
          hAinj (by rw [hAeq, hT, hT]; exact hb 0 g v)
        exact congrFun this i
      have hc : ∀ i : Fin n, ∃ a : ℂ, ∀ v, T v i = a • v := fun i => by
        obtain ⟨a, ha⟩ := hτ.2
          { toFun := fun v => T v i
            map_add' := fun v v' => by rw [hTadd]; rfl
            map_smul' := fun a v => by rw [hTsmul]; rfl } (fun g v => hTg g v i)
        exact ⟨a, fun v => by simpa using LinearMap.congr_fun ha v⟩
      choose c hc using hc
      have hrel : ∑ i, (Fin.cons (1 : ℂ) (fun j => -c j) : Fin (n + 1) → ℂ) i • b i = 0 := by
        rw [Fin.sum_univ_succ]
        ext v
        simp only [Fin.cons_zero, Fin.cons_succ, one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.zero_apply, neg_smul, Finset.sum_neg_distrib]
        rw [← hT v, hA]
        simp only [hc, map_smul]
        simp
      have := Fintype.linearIndependent_iff.1 hli _ hrel 0
      simp at this

private lemma indep_finset {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ)
    {κ : Type} (b : κ → (W' →ₗ[ℂ] W)) (hb : ∀ i, Intw τ ρ (b i)) (hli : LinearIndependent ℂ b)
    (s : Finset κ) (u : κ → W') (hu : ∑ i ∈ s, b i (u i) = 0) : ∀ i ∈ s, u i = 0 := by
  let e : Fin s.card ≃ s := s.equivFin.symm
  have h := indep_fin hτ s.card (fun j => b (e j)) (fun j => hb _)
    (hli.comp _ (Subtype.val_injective.comp e.injective)) (fun j => u (e j)) (by
      rw [e.sum_comp (fun i : s => b i (u i)), Finset.sum_coe_sort s fun i => b i (u i)]
      exact hu)
  intro i hi
  have := congrFun h (e.symm ⟨i, hi⟩)
  simpa using this

end SlopeTestRemainingChoices

section Main

variable {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def intwSub (τ : Representation ℂ G W') (ρ : Representation ℂ G W) : Submodule ℂ (W' →ₗ[ℂ] W) where
  carrier := {f | Intw τ ρ f}
  add_mem' {f f'} h h' g v := by simp [h g v, h' g v]
  zero_mem' g v := by simp
  smul_mem' a f h g v := by simp [h g v]

private lemma comm_inl (ρ : Representation ℂ (G × H) W) (g : G) (h : H) (w : W) :
    ρ (g, 1) (ρ (1, h) w) = ρ (1, h) (ρ (g, 1) w) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

private def kap (ρ : Representation ℂ (G × H) W) (τ : Representation ℂ G W') :
    Representation ℂ H (intwSub τ (ρ.comp (MonoidHom.inl G H))) where
  toFun h :=
    { toFun := fun φ => ⟨ρ (1, h) ∘ₗ φ.1, fun g v => by
        have := φ.2 g v
        simp only [LinearMap.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply] at this ⊢
        rw [this, comm_inl]⟩
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun a φ => by ext; simp }
  map_one' := by
    ext φ v
    show ρ (1, 1) (φ.1 v) = φ.1 v
    rw [Prod.mk_one_one, map_one]
    rfl
  map_mul' h h' := by
    ext φ v
    show ρ (1, h * h') (φ.1 v) = ρ (1, h) (ρ (1, h') (φ.1 v))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

private def evl (τ : Representation ℂ G W') (ρ : Representation ℂ G W) :
    W' ⊗[ℂ] intwSub τ ρ →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.flip (Submodule.subtype (intwSub τ ρ)))

private lemma evl_tmul (τ : Representation ℂ G W') (ρ : Representation ℂ G W) (w : W') (φ : intwSub τ ρ) :
    evl τ ρ (w ⊗ₜ φ) = φ.1 w := by
  simp [evl]

private lemma evl_inj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hτ : AbsIrr τ) :
    Function.Injective (evl τ ρ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  let B := Module.Basis.ofVectorSpace ℂ (intwSub τ ρ)
  let e := TensorProduct.equivFinsuppOfBasisRight (M := W') B
  have hz' : z = (e z).sum fun i w => w ⊗ₜ B i := by
    have := TensorProduct.equivFinsuppOfBasisRight_symm_apply B (e z)
    rw [← this, e.symm_apply_apply]
  have hsum : ∑ i ∈ (e z).support, (B i).1 (e z i) = 0 := by
    rw [← hz]
    conv_rhs => rw [hz']

    rw [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => (evl_tmul τ ρ _ _).symm
  have hli : LinearIndependent ℂ fun i => (B i).1 :=
    B.linearIndependent.map' (intwSub τ ρ).subtype (Submodule.ker_subtype _)
  have h0 := indep_finset hτ (fun i => (B i).1) (fun i => (B i).2) hli _ (e z) hsum
  have : e z = 0 := by
    ext i
    by_cases hi : i ∈ (e z).support
    · simpa using h0 i hi
    · simpa using hi
  simpa using this

private lemma evl_surj {τ : Representation ℂ G W'} {ρ : Representation ℂ G W} (hI : Isot ρ τ) :
    Function.Surjective (evl τ ρ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine hI.trans (iSup_le fun f => ?_)
  rintro _ ⟨w, rfl⟩
  exact ⟨w ⊗ₜ ⟨f.1, f.2⟩, evl_tmul τ ρ w ⟨f.1, f.2⟩⟩

end Main

theorem step :
    Step := by
  intro G H W W' _ _ _ _ _ _ ρ τ hτ hI
  refine ⟨intwSub τ (ρ.comp (MonoidHom.inl G H)), inferInstance, inferInstance, kap ρ τ,
    LinearEquiv.ofBijective (evl τ _) ⟨evl_inj hτ, evl_surj hI⟩, ?_⟩
  rintro ⟨g, h⟩ z
  show evl τ _ (box τ (kap ρ τ) (g, h) z) = ρ (g, h) (evl τ _ z)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul w φ =>
    have := φ.2 g w
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at this
    show evl τ _ (τ g w ⊗ₜ kap ρ τ h φ) = _
    rw [evl_tmul, evl_tmul]
    show ρ (1, h) (φ.1 (τ g w)) = _
    rw [this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end UpperTheory.V.Z.J.D
end
