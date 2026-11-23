module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardIdealRegularity
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle021
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_ideal_regularity : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (D : CartierDiv Y) (J : X.IdealSheafData), (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) → (∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → RegAt x f) → Nonempty ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)) ≅ idealModule J) := by
  first | exact @_root_.GlobalTheory.pushforward_twist_iso_idealModule | exact _root_.GlobalTheory.pushforward_twist_iso_idealModule | (intros; apply _root_.GlobalTheory.pushforward_twist_iso_idealModule <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_multiple_dominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  first | exact @_root_.GlobalTheory.effDominates | exact _root_.GlobalTheory.effDominates | (intros; apply _root_.GlobalTheory.effDominates <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_of_form : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  first | exact @_root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | exact _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic | (intros; apply _root_.GlobalTheory.Discrepancy.exists_isDivOfForm_and_toPic <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_cartier_local_equation : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData), FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧ ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0), J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := by
  first | exact @_root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier | exact _root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier | (intros; apply _root_.GlobalTheory.Cartier.IdealDiv.exists_cartierDiv_of_effCartier <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.order_at_codim_one_eq_one : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → a ≠ 0 → a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → t ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → Scheme.ord (fnOf U (gen_mem hz) a) z = 1 := by
  first | exact @_root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates | exact _root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates | (intros; apply _root_.GlobalTheory.Cartier.ord_fnOf_eq_one_of_generates <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.order_off_codim_one_eq_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U) (a t : Γ(X, U)), Order.coheight z = 1 → (∀ g ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal, ∃ r, t * g = a * r) → ∀ (v : X) (hv : v ∈ U), v ∈ X.basicOpen t → v ≠ z → Scheme.ord (fnOf U (gen_mem hv) a) v = 0 := by
  first | exact @_root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center | exact _root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center | (intros; apply _root_.GlobalTheory.Cartier.ord_fnOf_eq_zero_off_center <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.regular_sequence_prime_divisors : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  first | exact @_root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams | exact _root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams | (intros; apply _root_.GlobalTheory.RegParPrime.exists_primeDivisors_of_regularParams <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.serre_vanishing_snc_atlas : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | exact _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | (intros; apply _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.cartier_operator_log_sections : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ → CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s)) (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  first | exact @_root_.GlobalTheory.cartierAt_atlas_inter | exact _root_.GlobalTheory.cartierAt_atlas_inter | (intros; apply _root_.GlobalTheory.cartierAt_atlas_inter <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_multiple_below_threshold : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  first | exact @_root_.GlobalTheory.CoefBound.coef_lt_of_large | exact _root_.GlobalTheory.CoefBound.coef_lt_of_large | (intros; apply _root_.GlobalTheory.CoefBound.coef_lt_of_large <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory

private theorem exists_sec_lbPow_add_nonzeroLocus_eq_inf {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {m n : ℕ} (s : (lbPow L m).Sec) (s' : (lbPow L n).Sec) :
    ∃ τ : (lbPow L (m + n)).Sec, nonzeroLocus τ = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine ⟨powSecMk (m + n) (fun i => powSecFn s i * powSecFn s' i) ?_, ?_⟩
  · intro i j
    rw [map_mul, map_mul, powSecFn_compat s i j, powSecFn_compat s' i j, pow_add]
    ring
  · rw [nonzeroLocus_powSecMk]
    simp_rw [Scheme.basicOpen_mul, ← nonzeroLocus_inf_powSecFn]
    apply le_antisymm
    · exact iSup_le fun i => le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    · intro x hx
      have hx' : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx' ⊢
      obtain ⟨i, hi⟩ := hx'
      exact ⟨i, ⟨hx.1, hi⟩, ⟨hx.2, hi⟩⟩

theorem exists_sec_lbPow_nonzeroLocus_eq_iInf {X : Scheme.{0}} {H : LB X} (hH : H.IsLB)
    {r : ℕ} (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec) (he : ∀ a, 0 < e a)
    (t : Finset (Fin r)) (ht : t.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : (lbPow H N).Sec, nonzeroLocus τ = ⨅ a ∈ t, nonzeroLocus (σ a) := by
  induction t using Finset.cons_induction with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | cons a s ha ih =>
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨e a, he a, σ a, ?_⟩
      simp
    · obtain ⟨N, hN, τ, hτ⟩ := ih hs
      obtain ⟨τ', hτ'⟩ := exists_sec_lbPow_add_nonzeroLocus_eq_inf hH (σ a) τ
      refine ⟨e a + N, by omega, τ', ?_⟩
      rw [hτ', hτ, Finset.cons_eq_insert, Finset.iInf_insert]

theorem subsingleton_cohOn_preimage_iInf_nonzeroLocus : ∀ (X Y : Scheme.{0}) [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), H.IsLB → ∀ j : ℕ, (∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → ∀ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec), (∀ a, 0 < e a) → ∀ t : Finset (Fin r), t.Nonempty → Subsingleton (cohOn F (s ⁻¹ᵁ (⨅ a ∈ t, nonzeroLocus (σ a))) j) := by
  intro X Y _ _ s F _ H hH j hev r e σ he t ht
  obtain ⟨N, hN, τ, hτ⟩ := exists_sec_lbPow_nonzeroLocus_eq_iInf hH e σ he t ht
  rw [← hτ, ← nonzeroLocus_secPowPull τ s]
  have hM : (H.pull s).IsLB := LB.isLB_pull hH s
  have hL : (lbPow (H.pull s) N).IsLB := isLB_lbPow hM N
  apply subsingleton_cohOn_nonzeroLocus_of_eventually_twist Y F (lbPow (H.pull s) N) hL
  obtain ⟨c0, hc0⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨c0, fun c hc => ?_⟩
  have hcls : cls (lbPow (lbPow (H.pull s) N) c) (isLB_lbPow hL c)
      = cls (lbPow (H.pull s) (N * c)) (isLB_lbPow hM (N * c)) := by
    rw [CechPic.cls_lbPow hL, CechPic.cls_lbPow hM, CechPic.cls_lbPow hM, smul_smul, mul_comm]
  obtain ⟨iso⟩ := nonempty_twist_iso_of_cls_eq F (isLB_lbPow hL c) (isLB_lbPow hM (N * c)) hcls
  have hsub := hc0 (N * c) (le_trans hc (Nat.le_mul_of_pos_left c hN))
  exact (cohOn.mapIso (Γ(Y, ⊤)) ⊤ j iso).toEquiv.subsingleton

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.ideal_sections_locally_generated : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := by
  first | exact @_root_.GlobalTheory.Twist.exists_secs_generating_ideal | exact _root_.GlobalTheory.Twist.exists_secs_generating_ideal | (intros; apply _root_.GlobalTheory.Twist.exists_secs_generating_ideal <;> assumption)
end
