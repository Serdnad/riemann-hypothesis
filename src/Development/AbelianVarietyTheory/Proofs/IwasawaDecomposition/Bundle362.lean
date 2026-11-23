module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle345
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh.KStd

theorem K1_le_J0_empty {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) :
    K1 B.sp.cm n ST SG ≤ J0 B.sp.cm n ∅ := by
  intro t ht
  have h1 := principal_le_congruence_subgroup B.sp.cm n ST SG ht
  unfold J0 at h1 ⊢
  simp only [Subgroup.mem_inf] at h1 ⊢
  refine ⟨h1.1, ?_⟩
  simp

theorem exists_ptOf_mul_K1 : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  intro B n _ ST SG k t ht ⟨p, hp, hN⟩
  have hz : t ∈ J0 B.sp.cm n ∅ := K1_le_J0_empty n ST SG ht
  refine ⟨p, ?_, hN⟩
  refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw B.host.F B.host.E B.sp.cm n ∅ ∅ ∅ (k * t) p rfl).2 ⟨?_, ?_⟩
  · exact mul_mem hp.uni (congruence_le_adelic_unitary B.sp.cm n ∅ hz)
  · have h := decoRaw_rawSm B.sp.cm ∅ ∅ 1 (⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) k
    rw [map_one, map_inv] at h
    have e : Formalism.UG.bc (iA B.host.F B.host.E) ((1 : URat B.sp.cm n) : GL (Fin n) B.host.E) * k *
        (((⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) : J0 B.sp.cm n ∅) : GL (Fin n) (AfE B.host.F B.host.E))⁻¹ = k * t := by
      simp
    rw [e] at h
    have hr : (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹ = 1 := Subsingleton.elim _ _
    rw [hr] at h
    rw [(near_of_isPtOf hp 0).deco] at h
    simp only [map_one] at h
    change decoRaw ∅ ∅ (k * t) = Deco.act 1 1 p.deco.1 at h
    rw [Deco.act_one] at h
    exact h.symm

end GlobalTheory.Mem.Col2.TopCh.KStd

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdPlace

theorem bc_prV_eq_one_of_adAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (η : GL (Fin n) (AfE F E)), (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ i j, adAt F w (η.1 i j) = if i = j then 1 else 0) → bc (prV (E := E) v) η = 1 := by
  intro F E _ _ _ _ _ n v η h
  refine Units.ext (Matrix.ext fun i j => ?_)
  change prV (E := E) v (η.1 i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j
  rw [Matrix.one_apply, ← sub_eq_zero]
  have e : (if i = j then (1 : E ⊗[F] v.adicCompletion F) else 0) = prV (E := E) v (if i = j then 1 else 0) := by
    split_ifs <;> simp
  rw [e, ← map_sub]
  refine ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).1).2 fun w hw => ?_
  rw [map_sub, h w hw i j]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdPlace
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.FullDt
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E)

theorem mem_u1int_iff_entry (u : GL (Fin 1) (AfE F E)) :
    u ∈ Formalism.L2.Herm.IntegralUnitGroup hc ↔ u ∈ Formalism.L2.Herm.unitaryOneFiniteAdeles hc ∧ ∀ y : Fin 1 → AfE F E,
      (y 0 ∈ RInt F E ↔ (u : Matrix (Fin 1) (Fin 1) (AfE F E)) 0 0 * y 0 ∈ RInt F E) := by
  have hl : ∀ y : Fin 1 → AfE F E, y ∈ (Formalism.UG.stdLat (n := Fin 1) ↥(RInt F E) : Submodule ↥(RInt F E) (Fin 1 → AfE F E)) ↔
      y 0 ∈ RInt F E := by
    intro y
    simp only [Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_one]
    exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  show u ∈ Formalism.UG.UJ _ _ ⊓ Formalism.UG.stabGL _ ↔ _
  rw [Subgroup.mem_inf]
  refine and_congr Iff.rfl ?_
  show (∀ y, _ ↔ _) ↔ _
  refine forall_congr' fun y => ?_
  rw [hl, hl]
  simp [Matrix.mulVec, dotProduct]


omit [StarRing E] in
theorem rInt_mul_iff {c d : AfE F E} (hcd : c * d = 1) :
    (∀ y : AfE F E, y ∈ RInt F E ↔ c * y ∈ RInt F E) ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P c) = 1 := by
  constructor
  · intro h P
    have hc1 : c ∈ RInt F E := by simpa using (h 1).1 (one_mem _)
    have hd1 : d ∈ RInt F E := (h d).2 (by rw [hcd]; exact one_mem _)
    have a1 := (mem_rInt_iff F E c).1 hc1 P
    have a2 := (mem_rInt_iff F E d).1 hd1 P
    rw [← adAt_apply] at a1 a2
    have e : Valued.v (adAt F P c) * Valued.v (adAt F P d) = 1 := by rw [← map_mul, ← map_mul, hcd, map_one, map_one]
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  · intro h y
    rw [mem_rInt_iff, mem_rInt_iff]
    refine forall_congr' fun P => ?_
    rw [← adAt_apply, ← adAt_apply, map_mul, map_mul, h P, one_mul]
end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_u1int_iff_val : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E),
    IsDetLift (host_cmData R H) x.1 a → ((x.1 ∈ Formalism.L2.Herm.IntegralUnitGroup (host_cmData R H)) ↔
      ∀ w : HeightOneSpectrum (𝓞 H.E), Valued.v (compAt w a) = Valued.v (compAt (conjPrime₂ w) a)) := by
  intro R H x a ha
  have hcd : ((x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0) * ((x.1⁻¹ : GL (Fin 1) (AfE H.F H.E)) : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 1) (Fin 1) (AfE H.F H.E) => M 0 0) (Units.mul_inv x.1)
    simpa [Matrix.mul_apply] using this
  rw [mem_u1int_iff_entry, and_iff_right x.2]
  have e1 : (∀ y : Fin 1 → AfE H.F H.E, (y 0 ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y 0 ∈ RInt H.F H.E)) ↔
      ∀ y : AfE H.F H.E, (y ∈ RInt H.F H.E ↔ (x.1 : Matrix (Fin 1) (Fin 1) (AfE H.F H.E)) 0 0 * y ∈ RInt H.F H.E) :=
    ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩
  rw [e1, rInt_mul_iff hcd]
  refine forall_congr' fun w => ?_
  have k := congrArg Valued.v (DetSpec.compAt_eq ha w)
  rw [map_mul, valued_sigR, adAt_finAf, Matrix.det_fin_one] at k
  rw [k]
  have h0 := DetSpec.val_compAt_ne (conjPrime₂ w) a
  constructor
  · intro h; rw [h, one_mul]
  · intro h
    exact (mul_eq_right₀ h0).1 h
end GlobalTheory.Mem.Col2.FullDt

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.isPointOf_rational_unitary_adelic_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  first | exact @GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | (intros; apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.placeProjection_zero_integral_iff_components_above : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  first | exact @GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | exact GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff | (intros; apply GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.isPointOf_last_coordinate_dilation_one_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  first | exact @GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt | exact GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt | (intros; apply GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.PiDiv

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E}

theorem notMem_of_notMem (h : BasePi ST π) {w : Pl E} (hw : w ∉ ST) : π ∉ w.asIdeal := by
  intro hπ
  have hle : ST.inf (fun P : Pl E => P.asIdeal) ≤ w.asIdeal := by
    intro x hx
    have hx' : ∀ P ∈ ST, x ∈ P.asIdeal := fun P hP => (Finset.inf_le hP : ST.inf (fun P : Pl E => P.asIdeal) ≤ P.asIdeal) hx
    obtain ⟨c, rfl⟩ := (h.dvd x).1 hx'
    exact Ideal.mul_mem_right _ _ hπ
  obtain ⟨P, hP, hPw⟩ := (Ideal.IsPrime.inf_le' w.isPrime).1 hle
  have e : P.asIdeal = w.asIdeal := P.isMaximal.eq_of_le w.isPrime.ne_top hPw
  exact hw (HeightOneSpectrum.ext e ▸ hP)

theorem exp_neg_one_le (h : BasePi ST π) {w : Pl E} (hw : w ∈ ST) : WithZero.exp (-1) ≤ w.intValuation π := by
  classical
  obtain ⟨b, hb⟩ := w.intValuation_exists_uniformizer
  obtain ⟨a, ha⟩ := crtPl ST (fun P => if P = w then 1 else 0)
  have haw : a ∉ w.asIdeal := by
    intro haw
    have h1 := ha w hw
    rw [if_pos rfl] at h1
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ haw h1))
  have hbw : b ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem b).1 (by rw [hb, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  have hab : ∀ P ∈ ST, a * b ∈ P.asIdeal := by
    intro P hP
    by_cases hPw : P = w
    · subst hPw; exact Ideal.mul_mem_left _ _ hbw
    · have h1 := ha P hP
      rw [if_neg hPw, sub_zero] at h1
      exact Ideal.mul_mem_right _ _ h1
  obtain ⟨c, hc⟩ := (h.dvd _).1 hab
  have hv : w.intValuation (a * b) = WithZero.exp (-1) := by
    rw [map_mul, hb, HeightOneSpectrum.intValuation_eq_one_iff.2 haw, one_mul]
  rw [← hv, hc, map_mul]
  exact mul_le_of_le_one_right' (w.intValuation_le_one c)

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem prV_inclE (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) x) = inclE (F := F) (v.adicCompletion F) x := by
  simp [prV, inclE, Algebra.TensorProduct.map_tmul]

end GlobalTheory.Mem.Col2.PiDiv


open GlobalTheory.Mem.Col2.PiDiv in
theorem GlobalTheory.Mem.Col2.prV_eq_pi_mul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  intro F E _ _ _ _ _ _ ST π hπ v z hz hP
  set e : E := algebraMap (𝓞 E) E π with he_def
  have he : e ≠ 0 := hπ.coe_ne_zero
  have hzR : z ∈ RInt F E := hz
  refine ⟨prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e⁻¹ * z), ?_, ?_⟩
  · refine (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).2.2 fun w _ => ?_
    rw [map_mul, adAt_inclE, map_mul, valued_algebraMap, map_inv₀]
    have hz1 : Valued.v (adAt F w z) ≤ 1 := by rw [adAt_apply]; exact (mem_rInt_iff F E z).1 hzR w
    have hv0 : 0 < w.valuation E e := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 he
    rw [inv_mul_le_one₀ hv0]
    have hve : w.valuation E e = w.intValuation π := HeightOneSpectrum.valuation_of_algebraMap w π
    by_cases hw : w ∈ ST
    · exact (le_exp_neg_one_of_lt_one (hP w hw)).trans (hve ▸ exp_neg_one_le hπ hw)
    · rw [hve, HeightOneSpectrum.intValuation_eq_one_iff.2 (notMem_of_notMem hπ hw)]
      exact hz1
  · rw [map_mul, prV_inclE, ← mul_assoc, ← map_mul, mul_inv_cancel₀ he, map_one, one_mul]
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.rowFiniteTypes_isotypicParts_span_orthogonal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (P : principalLevelFrame.RowPsi V D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Inputs D → V.SigOK → IsInfFam θ → StdFrame hF P → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → (∃ (s : Finset (GA D V)) (c : GA D V → ℂ), (∀ g ∈ s, g ∈ GfC V) ∧ e = ∑ g ∈ s, c g • principalLevelFrame.rtA g) → (⨆ π, principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π) = goodPart θ M (levS V β L) (levChi V β L) e ∧ ∀ π π', ¬ π.Iso π' → ∀ x ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π, ∀ y ∈ principalLevelFrame.isotL θ P M (levS V β L) (levChi V β L) e π', ipM M μ 𝓕 x y = 0 := by
  first | exact @GlobalTheory.FinTypesRows.isotL_span_orth | exact GlobalTheory.FinTypesRows.isotL_span_orth | (intros; apply GlobalTheory.FinTypesRows.isotL_span_orth <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.RefTup

theorem qe_one_tup {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem twistPrimes_reference_tuple_eq_empty : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Q I.mu0 = ∅ := by
  intro B X I
  show QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅
  rw [I.trueColumn_tuple_trivial_eq_one]
  exact qe_one_tup I.sel

end GlobalTheory.Mem.Col2.RefTup
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem T_notMem_under_uSG : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word)
    (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ →
    (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  classical
  intro B X I hI u P hP hm
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hE : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    have h1 : ((B.T u : ℕ) : 𝓞 B.host.F) ∈ P.asIdeal.under (𝓞 B.host.F) := hm
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩ hE
  · have hg := (good_of_mem hI h).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 hE
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u

end GlobalTheory.Mem.LevTwist
end

section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_wdSide : GlobalTheory.Published.DeRhamPotSemistable → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (WDSide D T) :=
  fun hB D T => nonempty_wdSide_of_tie hB D T

end GlobalTheory.HeightCounting
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finiteVolume_adelicUnitaryQuotient : FiniteVolume₂ := by
  first | exact @GlobalTheory.Mem.VolFin.finVol | exact GlobalTheory.Mem.VolFin.finVol | (intros; apply GlobalTheory.Mem.VolFin.finVol <;> assumption)
end
