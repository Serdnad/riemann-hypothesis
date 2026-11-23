module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle477
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle307
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsHodgeCohomologyEquivCechDifferentials
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle308
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG


theorem _root_.GlobalTheory.T.adelicPoints_same_badComponents_same_localization : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) :=
  @GlobalTheory.TwV.AwayLat.lat_eq
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumnTupleKernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z → ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  first | exact @GlobalTheory.TwU.AtTrue.tuple_kernels_rational | exact GlobalTheory.TwU.AtTrue.tuple_kernels_rational | (intros; apply GlobalTheory.TwU.AtTrue.tuple_kernels_rational <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelCoefficientField_le_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  first | exact @GlobalTheory.TwU.kerField_le_rec | exact GlobalTheory.TwU.kerField_le_rec | (intros; apply GlobalTheory.TwU.kerField_le_rec <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.placeUnderTwistPrime_over_tupleRamifiedPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), I.UnderQ a v → ∃ q ∈ Y.Qp a, ((q : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
  first | exact @GlobalTheory.TwU.UnderQp.underQ_qp | exact GlobalTheory.TwU.UnderQp.underQ_qp | (intros; apply GlobalTheory.TwU.UnderQp.underQ_qp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.BaseComp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem star_int (r : 𝓞 E) : ∃ s : 𝓞 E, (s : E) = star (r : E) :=
  ⟨⟨star (r : E), r.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem mem_dual_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem fg_of_int (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) : L.FG := by
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  have hle : L ≤ LinearMap.range f := by
    intro x hx
    choose r hr using h x hx
    exact ⟨r, funext fun j => (hr j).symm⟩
  haveI : IsNoetherian (𝓞 E) (LinearMap.range f) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have := (isNoetherian_submodule.1 (inferInstance : IsNoetherian (𝓞 E) (LinearMap.range f))) L hle
  exact this

theorem sup_dual_eq_std (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E))
    (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    Lb ⊔ Ideal.span {c} • Formalism.HermitianLatticesTheory.dual (hStd E n) Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  have hst : star (t : E) ≠ 0 := by
    rw [star_ne_zero]; exact_mod_cast ht
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.smul_le]
      intro a ha y hy
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      have hx : (Pi.single j (t : E) : Fin n → E) ∈ Lb := by
        rw [hLb]
        intro k
        by_cases hk : k = j
        · subst hk; exact ⟨t, by simp, fun _ => dvd_refl t⟩
        · exact ⟨0, by simp [hk], fun _ => dvd_zero t⟩
      obtain ⟨r, hr⟩ := (mem_dual_iff Lb y).1 hy _ hx
      have hsum : ∑ k, star ((Pi.single j (t : E) : Fin n → E) k) * y k = star (t : E) * y j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hsum] at hr
      refine ⟨s * r, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hr]
      rw [show algebraMap (𝓞 E) E c = (c : E) from rfl, hc, mul_assoc]
  · intro x hx
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one] at hx
    choose r hr using hx
    let x' : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let w : Fin n → E := fun j => if j.1 + 1 = n then x j / star (t : E) else 0
    have hx' : x' ∈ Lb := by
      rw [hLb]
      intro j
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x', hj], fun _ => dvd_zero t⟩
      · exact ⟨r j, by simp [x', hj, hr j], fun h => absurd h hj⟩
    have hw : w ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) Lb := by
      rw [mem_dual_iff]
      intro z hz
      refine Subring.sum_mem _ fun k _ => ?_
      by_cases hk : k.1 + 1 = n
      · obtain ⟨q, hq, hdiv⟩ := (hLb z).1 hz k
        obtain ⟨d, rfl⟩ := hdiv hk
        obtain ⟨s, hs⟩ := star_int d
        refine ⟨s * r k, ?_⟩
        simp only [w, hk, if_true, hq]
        rw [map_mul, hr k, show algebraMap (𝓞 E) E s = (s : E) from rfl, hs]
        push_cast
        rw [star_mul', ← hr k]
        field_simp
      · exact ⟨0, by simp [w, hk]⟩
    have hxe : x = x' + c • w := by
      funext j
      by_cases hj : j.1 + 1 = n
      · simp only [x', w, hj, if_true, Pi.add_apply, Pi.smul_apply, zero_add]
        rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl, hc]
        field_simp
      · simp [x', w, hj]
    rw [hxe]
    exact Submodule.add_mem_sup hx' (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hw)

end GlobalTheory.TwU.BaseComp

open scoped TensorProduct

namespace GlobalTheory.TwU.BaseComp

theorem latCo_one_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (sp : Spaces R F E) (hσ : ∀ x, (sp.cm.sig : E →+* E) x = star x) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E)) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    GlobalTheory.TwU.latCo sp J 1 c 1 Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  subst hJ
  have hfg : Lb.FG := fg_of_int Lb fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have hA : Formalism.L2.PairingIndexBounds.F.latAd (F := F) (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb :=
    GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ Lb Lb (Module.Finite.iff_fg.2 hfg) (fun x => by simp)
  unfold GlobalTheory.TwU.latCo
  rw [hA]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual ((sp.cm.sig : E →+* E)) hσ Lb
  unfold dualL at key
  erw [key]
  exact sup_dual_eq_std t c ht hc Lb hLb

end GlobalTheory.TwU.BaseComp




theorem GlobalTheory.TwU.latCo_base_eq_stdL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), (∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N i) (X.piT u)) → GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) 1 Lb = StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i) := by
  intro B X I hI hP l Z u i hi Lb hLb
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have ht : X.piT u ≠ 0 := by
    intro h0
    have hc := l.pr.piT_cop u
    have h0' : (B.primes X).piT u = 0 := h0
    rw [h0', map_zero] at hc
    exact not_isCoprime_zero_zero hc
  exact GlobalTheory.TwU.BaseComp.latCo_one_base _ (fun x => rfl) _ hG (X.piT u) (B.fields.conjO (X.piT u)) ht rfl Lb hLb
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tw_e0_mu0_eq_eMu0_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id | exact GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id | (intros; apply GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_levelCharacter_eq_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  first | exact @GlobalTheory.TwU.StepZeroChr.chr_zero | exact GlobalTheory.TwU.StepZeroChr.chr_zero | (intros; apply GlobalTheory.TwU.StepZeroChr.chr_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_level_readAsReference : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  exact @GlobalTheory.Mem.Col2.TC.LevZero.lev_zero
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stab0_rec7_of_levelData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  first | exact @GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | exact GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | (intros; apply GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_hodge_cohomology_equiv_cech_differentials : ∃ e : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B) (a b : ℕ), hodgeH p a b ≃ₗ[ℂ] (cech fun I => omB ℂ Z.functionField (B I) a).H b,
  (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (hinst : inst = ffAlg p) (hU : IsAffCover p U B)
    (d' : ℕ) (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [SmoothOfRelativeDimension d' p'] [inst' : Algebra ℂ Z'.functionField] (κ : Type) [LinearOrder κ] [Fintype κ] (U' : κ → Z'.Opens) (B' : Finset κ → Subalgebra ℂ Z'.functionField) (hinst' : inst' = ffAlg p') (hU' : IsAffCover p' U' B')
    (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField) (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField) (τ : κ → ι),
    IsDRMap ℂ ψ φ → (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)), ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) → (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) →
    ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Z.functionField (B I) a) (cech fun I => omB ℂ Z'.functionField (B' I) a) (pullC τ φ)) (z : hodgeH p a b),
      e d' Z' p' κ U' B' hinst' hU' a b (hodgePull hf a b z) = Cx.hmap _ _ (pullC τ φ) hm b (e d Z p ι U B hinst hU a b z)) ∧
  (∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField] (Y : Scheme.{0}) [IsIntegral Y] (p' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d p'] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] (ι : Type) [LinearOrder ι] [Fintype ι] (U : ι → Z.Opens) (B : Finset ι → Subalgebra ℂ Z.functionField) (B' : Finset ι → Subalgebra ℂ Y.functionField) (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p') (hU : IsAffCover p U B) (hU' : IsAffCover p' (fun i => c ⁻¹ᵁ U i) B'),
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (a b : ℕ) (hm : IsMap (cech fun I => omB ℂ Y.functionField (B' I) a) (cech fun I => omB ℂ Z.functionField (B I) a) (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s))) (z : hodgeH p' a b),
      e d Z p ι U B hinst hU a b (hodgeTrace hc a b z) = Cx.hmap _ _ (LinearMap.pi fun s : Finset ι => (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField).comp (LinearMap.proj s)) hm b (e d Y p' ι (fun i => c ⁻¹ᵁ U i) B' hinst' hU' a b z)) := by
  first | exact @UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials | exact UpperTheory.Cb.exists_hodge_cohomology_equiv_cech_differentials
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open scoped Pointwise

namespace GlobalTheory.AboveL

theorem mem_dec_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : _root_.Formalism.ConjugateSelfDual.G K Ω) (g' : _root_.Formalism.ConjugateSelfDual.G K' Ω) (hg : ∀ x, g x = g' x) :
    g ∈ _root_.ReciprocityTheory.Gal.Dec (F := K) A ↔ g' ∈ _root_.ReciprocityTheory.Gal.Dec (F := K') A := by
  have key : ((g • A : ValuationSubring Ω) : Set Ω) = ((g' • A : ValuationSubring Ω) : Set Ω) := by
    rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]
  unfold _root_.ReciprocityTheory.Gal.Dec
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; apply SetLike.coe_injective; rw [← key]; exact congrArg _ h
  · intro h; apply SetLike.coe_injective; rw [key]; exact congrArg _ h

theorem exists_cm_solvable_split : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w), ∀ N : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω), IsOpen (N : Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ _root_.ReciprocityTheory.Gal.Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ _root_.ReciprocityTheory.Gal.Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  intro Ω _ E _ _ _ _ _ A w h N hN
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := Ideal.comap_ne_bot_of_integral_mem hx₀0 hx₀ (Algebra.IsIntegral.isIntegral x₀) }
  have hv : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v := by
    intro x
    show _ ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [← h]
    rfl
  obtain ⟨T, hvT, hlift⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hN

  let φ := IsScalarTower.toAlgHom F E Ω
  let K : IntermediateField F Ω := φ.fieldRange
  haveI : FiniteDimensional F K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  have hK : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, g ∈ K.fixingSubgroup ↔ ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x; exact hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩; exact hg x
  let V : Subgroup (_root_.ReciprocityTheory.Gal.Dec (F := F) A) := K.fixingSubgroup.subgroupOf (_root_.ReciprocityTheory.Gal.Dec (F := F) A)
  have hVo : IsOpen (V : Set (_root_.ReciprocityTheory.Gal.Dec (F := F) A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
  haveI : Fact (Nat.card (E ≃ₐ[F] E)).Prime :=
    ⟨by rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E]; exact Nat.prime_two⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card rfl
  have habel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ := fun σ τ => (IsCyclic.commGroup).mul_comm σ τ
  have hcomm : commutator (_root_.ReciprocityTheory.Gal.Dec (F := F) A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mem_subgroupOf, hK]
    intro x
    have h1 : AlgEquiv.restrictNormalHom (K₁ := Ω) E ((a * b * a⁻¹ * b⁻¹ : _root_.ReciprocityTheory.Gal.Dec (F := F) A) : _root_.Formalism.ConjugateSelfDual.G F Ω) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [habel (AlgEquiv.restrictNormalHom E (a : _root_.Formalism.ConjugateSelfDual.G F Ω)) (AlgEquiv.restrictNormalHom E (b : _root_.Formalism.ConjugateSelfDual.G F Ω))]
      group
    have h2 := AlgEquiv.restrictNormal_commutes ((a * b * a⁻¹ * b⁻¹ : _root_.ReciprocityTheory.Gal.Dec (F := F) A) : _root_.Formalism.ConjugateSelfDual.G F Ω) E x
    have h3 : AlgEquiv.restrictNormal ((a * b * a⁻¹ * b⁻¹ : _root_.ReciprocityTheory.Gal.Dec (F := F) A) : _root_.Formalism.ConjugateSelfDual.G F Ω) E = 1 := h1
    rw [← h2, h3]
    rfl
  obtain ⟨F₁, hF₁fin, hF₁ab, hF₁real, hF₁dec, hF₁T⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F A v hv V hVo hcomm T hvT
  obtain ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, hfix, hsub⟩ :=
    hlift F₁ hF₁fin inferInstance (isSolvable_of_comm fun a b => hF₁ab.toIsMulCommutative.is_comm.comm a b) hF₁real hF₁T
  have hkey : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A → (∀ z ∈ F₁, g z = z) →
      ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g hg hz
    exact (hK g).1 (Subgroup.mem_subgroupOf.1 ((hF₁dec ⟨g, hg⟩).1 ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hz)))
  have hkey2 : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, g ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A → (∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) →
      ∀ z ∈ F₁, g z = z := by
    intro g hg hE
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hF₁dec ⟨g, hg⟩).2 (Subgroup.mem_subgroupOf.2 ((hK g).2 hE)))
  refine ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, ?_, ?_⟩
  · intro g hg
    apply (hfix g).2
    let g' : _root_.Formalism.ConjugateSelfDual.G F Ω := g.restrictScalars F
    have hg' : g' ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    exact hkey2 g' hg' (fun x => g.commutes x)
  · intro g hg
    have hfixP : ∀ x ∈ maximalRealSubfield M, g (algebraMap M Ω x) = algebraMap M Ω x :=
      fun x hx => g.commutes ⟨x, hx⟩
    have hF1 : ∀ z ∈ F₁, g z = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hsub z hz
      exact hfixP x hx
    have hFfix : ∀ y : F, g.toRingEquiv (algebraMap F Ω y) = algebraMap F Ω y :=
      fun y => hF1 _ (F₁.algebraMap_mem y)
    let g' : _root_.Formalism.ConjugateSelfDual.G F Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hFfix
    have hg' : g' ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    have hE : ∀ x : E, g.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := hkey g' hg' hF1
    let g'' : _root_.Formalism.ConjugateSelfDual.G E Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hE
    exact (hfix g'').2 hF1

end GlobalTheory.AboveL
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i c (p : Pl0 → D.what₂.LL[X]) (sX : A.ok A.μ0 × ℕ → D.what₂.LL) (sV : A.ok A.μ0 × ℕ → D.what₂.LL), (A.fam.R A.μ0).HasRes p sX → ∀ hX hV, IsOpsX R A.μ0 hX → IsOpsV R i A.μ0 hV → ∀ w ∈ EEc R SF c, LinearMap.adjoint (R.Th A.μ0) w ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ D.sp.X'.rank → hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A.μ0) w) = D.what₂.embLL (sX (P, k)) • LinearMap.adjoint (R.Th A.μ0) w) → ∀ y, R.thG i A.μ0 y ∈ Wcc R SF i c → R.thG i A.μ0 y ≠ 0 → (∀ (P : A.ok A.μ0) k, k ≤ (Vc D i).rank → hV (R.pl P) (Finsupp.single (splitLab (Vc D i).rank k) 1) y = D.what₂.embLL (sV (P, k)) • y) → (A.fam.L i A.μ0).HasRes (A.fam.tr i p) sV := by
  first | exact @GlobalTheory.Hk3.Link.hasRes_lift | exact GlobalTheory.Hk3.Link.hasRes_lift | (intros; apply GlobalTheory.Hk3.Link.hasRes_lift <;> assumption)
end
