module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistScalarField

open NumberField IsDedekindDomain

theorem val_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (χ₁ * χ₂).val v = χ₁.val v * χ₂.val v :=
  by rfl

theorem onId_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := by
  unfold Formalism.L2.Host.HChar.onId
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := L) I)
  have hs : ∀ χ : Formalism.L2.Host.HChar L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v I).Finite :=
    fun χ => hfin.subset fun v hv h0 => hv (by show χ.val v ^ _ = 1; rw [h0, zpow_zero])
  rw [← finprod_mul_distrib (hs χ₁) (hs χ₂)]
  exact finprod_congr fun v => by rw [val_mul, mul_zpow]

theorem onId_mem_range {L C : Type} [Field L] [NumberField L] [Field C] (emb : C →+* ℂ) (ξ : Formalism.L2.Host.HChar L)
    (h : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ emb.range) (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    ((ξ.onId I : ℂˣ) : ℂ) ∈ emb.range := by
  let S : Subgroup ℂˣ :=
    { carrier := {u | (u : ℂ) ∈ emb.range}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul]⟩
      one_mem' := ⟨1, by rw [map_one, Units.val_one]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨x, hx⟩ := ha
        exact ⟨x⁻¹, by rw [map_inv₀, hx, Units.val_inv_eq_inv_val]⟩ }
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), ξ.val v ∈ S := fun v => h _
  exact finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) (fun v => S.zpow_mem (hv v) _)



theorem twist_scalar_mem_range : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∃ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv htup hQG hF0 hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h N hU hTb hTl hLevOK hconj e Ps yd hh he hPs hPsO hs hy hcard
  classical
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.p.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.J.toCore.good_σ₀).1
  have hInR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hlev := hT.sh.dLev _ hInR (Vc D i).rank
  obtain ⟨pp, -, hpd⟩ := hT.sh.dPd
  have hpd1 := hRun.2.1
  rw [hpd _ hInR] at hpd1
  have hpd2 : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).pd = ownAt D v := by rw [hpd _ hInR, hpd1]
  have hL := hC.lev
  have hstd := hO.2.lift.std
  have hbadO := hO.2.bad ()
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad () := ⟨_, rfl⟩
  have hbPs : ∀ PP ∈ Ps, ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP hm => by
    rw [hb, Nat.cast_mul (badN D * _)] at hm
    rcases PP.isPrime.mem_or_mem hm with h1 | h1
    · exact hPs PP hP h1
    · exact hPsO PP hP h1
  have h2b : 2 ∣ b := hb ▸ dvd_mul_of_dvd_right hbadO.2.1 _
  have hMb' : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∣ b := hb ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have g := GlobalTheory.AdTh.SerOne.guard_of_splitOffBad (Vc D i) hstd.1 hstd.2 _ h2b hMb' ⟨hh, e, Ps, he, hbPs, hs⟩
  obtain ⟨gU, ⟨k, hk1, hk2, hk3⟩, gS⟩ := g
  have gT : (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank).TrivAt ((O i).bad ()) :=
    ⟨k, Nat.Coprime.coprime_dvd_right (hb ▸ dvd_mul_left _ _) hk1, hk2, hk3⟩
  have hΛ : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) := by
    cases Λ with
    | mk La => congr 1; ext w; exact hconj w
  have memb : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((b : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := fun Q hQ => by
    rw [hb, hlev.2.1, hpd2, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hQ))
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal (Vc D i) hstd.1 hstd.2 h e Ps yd he hs hy b hbPs
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹)
    (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) hK.chr hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ hbadO.2.2.2.2)
        rw [hb, hu]
        simp only [Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hj))
      have a2 : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt Q := by
        by_contra hn
        rcases (hK.ram Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (memb Q (Finset.mem_filter.1 a).2)
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (memb Q' (Finset.mem_filter.1 a).2)
      change (R.C.mu0 i).loc Q x * (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).loc Q x * ((R.C.eta).loc Q x)⁻¹ = 1
      rw [a1 x hx, a2 x hx, R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, hK.triv.1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.2.ep ()).2 _ cc gU gT gS c1 c3
  have c2' : cc ⊔ Ideal.span {(((O i).bad () : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    refine top_le_iff.1 (c2 ▸ sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 ?_) _)
    rw [hb]; exact Nat.cast_dvd_cast (dvd_mul_left _ _)
  have hB := (hO.2.tuple ()).B cc c0 c2'
  have hxi : R.xiH A.μ0 = 1 := hL.xi_base
  have S1 : ∀ (χ₁ χ₂ : Formalism.L2.Host.HChar D.host.E) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := fun χ₁ χ₂ I => onId_mul χ₁ χ₂ I
  have S2 : ∀ (ξ : Formalism.L2.Host.HChar D.host.E), (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) →
      ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, ((ξ.onId I : ℂˣ) : ℂ) ∈ D.what₂.embLL.range :=
    fun ξ hξ I => onId_mem_range D.what₂.embLL ξ hξ I
  have e1 : R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹ =
      (R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹) * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) := by
    rw [hxi, mul_one, mul_right_comm]
  rw [e1, S1, Units.val_mul] at c4
  obtain ⟨a3, ha3⟩ := S2 _ hdel (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  have hF := hO.1
  have memF : ∀ x : (O i).c'.F, ∃ a : D.what₂.LL, D.what₂.embLL a = (x : ℂ) := fun x => by
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 ((SetLike.ext_iff.1 hF (x : ℂ)).1 x.2)
    exact ⟨a, ha⟩
  obtain ⟨a1, ha1⟩ := memF (incF T.Q.c (O i).c' (O i).hle (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))
  obtain ⟨a2, ha2⟩ := memF ((O i).B () cc)
  have hi : GlobalTheory.ClassScalarCompare.stdIndex Λ =
      GlobalTheory.ClassScalarCompare.stdIndex (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank) := by
    rw [hΛ]; exact GlobalTheory.ClassScalarCompare.stdIndex_conjLat _
  have q1' : (q : ℝ) ^ 2 * ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) := by
    rw [hi, hpq]; exact_mod_cast q1
  have hsq : ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ) =
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) * ((q : ℂ))⁻¹ := by
    have hq : (0:ℝ) < q := by exact_mod_cast q0
    have e2 : ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) / (q : ℝ) ^ 2 := by
      rw [← q1']; field_simp
    rw [e2, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hq.le, Complex.ofReal_div, div_eq_mul_inv,
      Complex.ofReal_ratCast]
  have h1 : (O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ) = D.what₂.embLL a1 := ha1.symm
  beta_reduce at hB
  have h2 := ha2.trans hB
  refine ⟨a1⁻¹ * a2 * a3 * ((q⁻¹ : ℚ) : D.what₂.LL), ?_⟩
  change _ = _ * _ * ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ)
  rw [h1, c4, hsq, map_mul, map_mul, map_mul, map_inv₀, map_ratCast, h2, ha3]
  push_cast
  ring

end GlobalTheory.TwistScalarField
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.EvAdm
open scoped Classical

theorem basisS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (W : Set (κ → FiniteAdeleRing (𝓞 F) F)),
    W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) → ∃ a : F, a ≠ 0 ∧ (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ W :=
  GlobalTheory.T.exists_scaledIntegralFiniteAdelePoints_subset_nhds

theorem boxS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) :=
  GlobalTheory.T.indicator_coset_scaledIntegral_eq_restrictedProduct

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => basisS F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := basisS F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  refine ⟨a, ha, ?_⟩
  set U := scaledInt F κ a
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ U} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt a).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hg.2 _ hN
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, funext fun x => ?_⟩
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have h := hinv r0 (x - r0) hxr0
      rw [add_sub_cancel] at h
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem (show x ∈ {y | y - r0 ∈ U} from hxr0), mul_one, h]
    · intro r hr hne
      have hm : x ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]
  · push Not at hx
    have hK : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    have hm : x ∉ {y | y - r ∈ U} := hx r hr
    simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose φ hSB hstd hφ using fun r : κ → FiniteAdeleRing (𝓞 F) F => boxS F κ a r ha
  let e := R.equivFin
  refine ⟨R.card, fun k => g (e.symm k), fun k => φ (e.symm k), fun k v => hSB _ v, fun k => hstd _, ?_⟩
  have hind : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y => ∏ᶠ v, φ r v fun i => evalV F v (y i) := fun r => funext (hφ r)
  refine hR.trans ?_
  simp only [hind]
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp e.symm (fun x : R => g x • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ x v fun i => evalV F v (y i))).symm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE l hl g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have hψSB : ∀ k v, ev v (φ k v) ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → Fv F v) := fun k v =>
    (hev v).2 ▸ Submodule.mem_map_of_mem (hφSB k v)
  have hψstd : ∀ k, ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun k =>
    ((hφvac k).and hM₁.std).mono fun v h => by rw [h.1, (hev v).1, h.2]
  have hg' : ∀ k, (fun y : Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := fun k =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB k) (hψstd k),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB k) (hψstd k)⟩
  choose T hT using fun k => hl _ (hg' k)
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφvac k)

  simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, hT, FunLike.coe_sum, Finset.sum_apply,
  FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]

end GlobalTheory.EvAdm

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

end GlobalTheory.MixUniq
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description | exact GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description | (intros; apply GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description <;> assumption)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.thetaGridBlockCongruence_typePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∈ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (∀ a b, Formalism.L2.DIV.blkOf D.R.r D.R.t b < Formalism.L2.DIV.blkOf D.R.r D.R.t a → valuation (Kw w) (g.1 a b) < 1) ∧ ∀ a b : Fin ((locGrid G t w).rank (0, j)), a.val < D.R.r → b.val < D.R.r → valuation (Kw w) ((g.1 - 1) a b) < 1 := by
  first | exact @GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description | exact GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description | (intros; apply GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description <;> assumption)
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.linearSection_etale_of_squarefree_chowForm : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  first | exact @GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | exact GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | (intros; apply GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare <;> assumption)
end
