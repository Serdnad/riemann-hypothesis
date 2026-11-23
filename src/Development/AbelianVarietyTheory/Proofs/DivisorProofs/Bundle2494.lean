module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle840
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle836
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle606
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle913
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



namespace GlobalTheory.BaseCmp

theorem dil_mem_latP (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ϖ : 𝓞 D.host.E) : ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  intro y hy
  have hint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := by
    have e : finPart D (incA D (ϖ : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (ϖ : D.host.E) := rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simpa using (one_mem (v.adicCompletionIntegers D.host.F)), ϖ, rfl⟩
  have h := GlobalTheory.LatticeStable.smul_mem_latO D (Vc D i) (Wc D i) _ _ _ (incA D (ϖ : D.host.E)) hint y hy
  exact h

end GlobalTheory.BaseCmp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLiftRed

open GlobalTheory.AdelicLatMove

theorem idem_smul_mem_latO {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (sdS : IsSelfDualC S ΛS) (frS : Formalism.L2.DIV.IsFrame βS ΛS) (frT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) {a : 𝓞 D.host.E} (ha : a ∉ P.asIdeal)
    (haA : (a : D.host.E) ∈ D.host.AA) {x : WO S T} (hx : IsIntM (frMapO S T βS βT x)) :
    e • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using GlobalTheory.IntHalfLat.exists_dual sdS frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (x.map (toEAf D)) βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT := fun j => by
    refine (frT _).2 fun i => ?_
    have e1 : Matrix.mulVec (βT⁻¹).val (fun i => Y i j) i = frMapO S T βS βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T ΛS ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by

    rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

end GlobalTheory.HalfLiftRed

theorem GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i _ Q hQ eQ he ϖ hϖ _ x
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, hQt⟩ := hQ
  have he2 := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ Q, ∀ PP' (hPP' : PP' ∈ Q),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (GlobalTheory.PlaceVec.isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : ↥Q) (j : Fin (Wc D i).rank) (k : Fin (Vc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.1.asIdeal) (x PP j k)
  set Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (EAf D) := fun j k =>
    ((⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) with hZ
  have hZe : ∀ j k, toEAf D eQ * Z j k = Z j k := fun j k => by
    simp only [hZ, MulMemClass.coe_mul]
    rw [← mul_assoc, ← RingHom.map_mul, he2]
  obtain ⟨w, hwh, -, hwZ⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) eQ he2 Z hZe
  have hint : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) := fun j k => by
    rw [hwZ]; exact Subtype.prop _
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using hϖ
  have hdil : dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ w) = w := by
    ext j k
    simp only [Matrix.map_apply]
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hϖE, RingHom.map_one, one_mul]
  refine ⟨dil i (ϖ : D.host.E)⁻¹ w, fun j k => ?_, ?_, fun PP => ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hwh j k]
  · rw [hdil]
    have hxe : (∑ PP ∈ Q, es PP) • w = w := by
      rw [← h2]; exact Matrix.ext fun j k => hwh j k
    rw [← hxe, Finset.sum_smul]
    refine sum_mem fun PP hPP => ?_
    have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hm =>
      hQG.2 t0 PP (hQt hPP) (by
        push_cast
        exact Ideal.mul_mem_left _ _ hm)
    refine GlobalTheory.HalfLiftRed.idem_smul_mem_latO hSV hFV hFW (h1 PP hPP) hN ?_ hint
    rw [show (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _]
    exact normK_mem_AA D
  · rw [hdil]
    funext j k
    unfold redM
    rw [dite_eq_left (by rw [hwZ]; exact Subtype.prop _)]
    have hsub : (⟨frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w j k, by rw [hwZ]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) := Subtype.ext (congrArg (fun M => M j k) hwZ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsub, RingHom.map_mul, hres PP.1 PP.2, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single PP]
    · rw [hdel PP.1 PP.2 PP.1 PP.2, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP.1 PP.2 b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



noncomputable section

namespace GlobalTheory.DilFlat

theorem eToEAf_int' {D : D7} (x : 𝓞 D.host.E) : eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩)

theorem isSBHalf_dilFlat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξR Q _ eQ hq ϖ hϖ _ Gc
  suffices hΦ : IsSBHalf eQ (lattice₂ R i) (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun v hv hv' t => by simp only [h2 v hv hv' t],
      fun t ht => h3 t (right_ne_zero_of_mul ht)⟩
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hϖE).map _
  have hc : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := eToEAf_int' ϖ
  have hfr : ∀ x : WO (Vc D i) (Wc D i), ∀ a b,
      frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x) a b =
        eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b := by
    intro x a b
    have hm : ((dil i (ϖ : D.host.E) x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D)) =
        eToEAf D (ϖ : D.host.E) • (x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D) := by
      ext a' b'
      simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hhalf : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (dil i (ϖ : D.host.E) x) ↔ IsHalf eQ x := by
    intro x
    refine ⟨fun h a b => hu.mul_left_cancel ?_, fun h a b => ?_⟩
    · have := h a b
      simp only [dil, Matrix.map_apply] at this
      rw [← this]; ring
    · simp only [dil, Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have key : (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) = fun x =>
      if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)) then
        omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)))
      else 0 := by
    funext x
    unfold flatDat
    by_cases h : IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    · rw [if_pos h, if_pos ⟨(hhalf x).2 h.1, h.2⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨(hhalf x).1 h'.1, h'.2⟩]
  rw [key]
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (fun x => frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    ?_ ?_ ?_ Q _ fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h
  · intro x u k a b
    simp only [hfr, GlobalTheory.PlaceDatum.frMapO_add]
    ring
  · obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg (R.βV i) (R.βW i)
    refine ⟨M, hM, fun u hu' a b => ?_⟩
    simp only [hfr]
    rw [mul_left_comm]
    exact mul_mem hc (h u hu' a b)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sV)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW) (R.βV i) (R.βW i)
    have hI : Ideal.span {ϖ} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hϖ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {ϖ}))
    set n := Ideal.absNorm (Ideal.span {ϖ})
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    have hnE : eToEAf D ((y : 𝓞 D.host.E) : D.host.E) * eToEAf D (ϖ : D.host.E) = (n : EAf D) := by
      rw [← RingHom.map_mul, ← map_natCast (eToEAf D)]
      congr 1
      exact_mod_cast hy
    refine ⟨K * n, Nat.mul_pos hK hn, fun t ht hti => ?_⟩
    have hnt : IsHalf eQ (n • t) := fun a b => by
      change eQ * (n • t a b) = n • t a b
      rw [mul_smul_comm, ht a b]
    have hfn : ∀ a b, frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (n • t) a b =
        (n : EAf D) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) t a b := fun a b => by
      have := GlobalTheory.PlaceDatum.frMapO_add (R.βV i) (R.βW i) 0 t n a b
      rw [zero_add] at this
      rw [this]
      simp [frMapO]
    rw [← smul_smul]
    refine h _ (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hnt) fun a b => ?_
    rw [hfn, ← hnE, mul_assoc, ← hfr]
    exact mul_mem (eToEAf_int' y) (hti a b)

end GlobalTheory.DilFlat

end
end

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp




attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLevelPf

variable {D : D7} {S T : HSp D}

theorem series_om_fin {B : Base S T} (hB : B.Good) {χS χT : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (hω : IsWeilDatumO B.F.ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (h : GA D S)
    (P : PolF D T.rank S.rank) (g : GA D T) {κ : GA D T} (hκ : κ ∈ GfC T) :
    series B.F ω (ω (1, κ) f) h P g = series B.F ω f h P (g * κ) := by
  rw [series_apply, series_apply]
  have e : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, Frame.fock, Frame.fock,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO B.F.ψ S T χS χT ω hω B.F.θ hB.frame.vac.2.inf 1 (one_mem _) κ hκ _ _ _ _ f P hf]

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

theorem rTup_datWp_val (x : GL (Fin (Wc D i).rank) (EAf D)) (PP : ↥(R.datWp i R.triv).Pg) (a b : Fin (R.datWp i R.triv).r) :
    (rTup (R.βW i) (R.datWp i R.triv) x PP).val a b =
      (redFn (R.βW i) PP.1 x).val (Fin.castLE (R.datWp i R.triv).hr a) (Fin.castLE (R.datWp i R.triv).hr b) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hm : redFn (R.βW i) PP.1 x ∈ blockTri (blk2 (R.datWp i R.triv).r) := by
    refine mem_blockTri.2 fun c d hcd => ?_
    have hc : c.val < (R.datWp i R.triv).r := lt_of_lt_of_eq c.2 rW
    have e : blk2 (R.datWp i R.triv).r c = 0 := if_pos hc
    exact absurd (lt_of_lt_of_eq hcd e) (Nat.not_lt_zero _)
  unfold rTup
  rw [upper_block_val_submatrix _ hm]
  rfl

theorem red_of_rTup (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g) : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x := by
  intro PP
  have hP : PP.1 ∈ R.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := congrArg (fun y : G0 (R.datWp i R.triv).Pg (R.datWp i R.triv).r => (y ⟨PP.1, hP⟩).val (Fin.cast (rank_Wc i) a)
    (Fin.cast (rank_Wc i) c)) hx
  simp only at h1
  rw [rTup_datWp_val] at h1
  rw [hent g PP.1 PP.2 hP a c]
  exact h1.symm.trans (by rw [hB.βT]; rfl)

theorem rTup_of_red (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x) : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g := by
  funext PP
  have hP : PP.1 ∈ B.G.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := hent g PP.1 hP PP.2 (Fin.cast (rank_Wc i).symm a) (Fin.cast (rank_Wc i).symm c)
  rw [hx ⟨PP.1, hP⟩, hB.βT] at h1
  rw [rTup_datWp_val]
  exact h1

theorem lifts_of_datWp (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) {g : G} {κ : GA D (Wc D i)}
    (hκ : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) : GlobalTheory.ExportType.Lifts B (e g) κ :=
  ⟨hκ.1, hB.βT ▸ parLev_St hκ.2.1, red_of_rTup hB e hent g _ hκ.2.2⟩

theorem exists_lift_datWp (hB0 : B.Good) (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) :
    ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.TypeSupportLift.exists_lift_supp B hB0 (e g)
  have h1 := GlobalTheory.FlatVecSum.levelLift_isLift_principalLevelDatum_realisation hB hκ
  rw [rTup_of_red hB e hent g _ (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ).red] at h1
  exact ⟨κ, h1⟩

end Real

theorem traceLevel : GlobalTheory.BaseCmp.TraceLevel := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i B hB hBo U ψ e hent hU hchi ω hω hh P
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (GlobalTheory.FlatVecSum.princ B).vecBase :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) (Base.admissible_empty_of_good (GlobalTheory.FlatVecSum.princ_good hB)) _)
      hB.frame.vac.2.theta
  have hsum : B.vecBase = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have := GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) (Twist.triv_good splitSet_empty) (Base.admissible_empty_of_good hB)
      (ω := ω) hω (fun p => (hlift (e.symm p)).choose) (fun p => by
        have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
        rwa [MulEquiv.apply_symm_apply] at this)
    rwa [Base.vecFlat_triv, Base.vecFlat_triv] at this
  funext x
  have hL : levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : B.theta ω hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift (e.symm p)).choose) := by
    rw [Base.theta, hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dite_eq_right, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dite_eq_left hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceLevelPf
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.existsUnique_forms_functional_abelian_base_change : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  first | exact @GlobalTheory.BaseChangeForm.existsUnique_functional | exact GlobalTheory.BaseChangeForm.existsUnique_functional | (intros; apply GlobalTheory.BaseChangeForm.existsUnique_functional <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



theorem _root_.GlobalTheory.T.completedPairLattice_dilation_mem_of_integer : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (ϖ : 𝓞 D.host.E), ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  first | exact @GlobalTheory.BaseCmp.dil_mem_latP | exact GlobalTheory.BaseCmp.dil_mem_latP | (intros; apply GlobalTheory.BaseCmp.dil_mem_latP <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



theorem _root_.GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  first | exact @GlobalTheory.DilFlat.isSBHalf_dilFlat | exact GlobalTheory.DilFlat.isSBHalf_dilFlat | (intros; apply GlobalTheory.DilFlat.isSBHalf_dilFlat <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



theorem _root_.GlobalTheory.T.exists_half_dilated_reduction_residueMatrices : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  first | exact @GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | exact GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | (intros; apply GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq <;> assumption)

end
end

section

@[expose] public section


theorem _root_.GlobalTheory.T.thetaTraceLevelCompatible_proof : GlobalTheory.BaseCmp.TraceLevel := by
  first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)

end
end
