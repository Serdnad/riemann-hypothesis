module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle004
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlgQ

theorem exists_den {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ s ∈ nonZeroDivisors R, s • v ∈ M := by
  have hv : v ∈ Submodule.span K (M : Set V) := by rw [hM]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact M.add_mem (M.smul_mem _ hsx) (M.smul_mem _ hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective R a
    refine ⟨d * s, mul_mem hd hs, ?_⟩
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
    have h1 : (d * s) • ((algebraMap R K n / algebraMap R K d) • x) = n • (s • x) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h1]
    exact M.smul_mem _ hsx

theorem finrank_quot_eq {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    finrank R (M ⧸ (W.restrictScalars R).comap M.subtype) = finrank K (V ⧸ W) := by
  let g : M →ₗ[R] (V ⧸ W) := (W.mkQ.restrictScalars R).comp M.subtype
  have hker : LinearMap.ker g = (W.restrictScalars R).comap M.subtype := by
    ext x
    simp [g]
  let f : (M ⧸ (W.restrictScalars R).comap M.subtype) →ₗ[R] (V ⧸ W) :=
    Submodule.liftQ _ g (le_of_eq hker.symm)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hker)
  have hloc : IsLocalizedModule (nonZeroDivisors R) f := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [hinj h]⟩⟩
    · have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← algebraMap_smul K (s : R) a, ← algebraMap_smul K (s : R) b] at hab
        exact smul_right_injective _ hs0 hab
      · intro a
        refine ⟨(algebraMap R K s)⁻¹ • a, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs0, one_smul]
    · obtain ⟨v, rfl⟩ := W.mkQ_surjective y
      obtain ⟨s, hs, hsv⟩ := exists_den (K := K) M hM v
      refine ⟨(Submodule.Quotient.mk ⟨s • v, hsv⟩, ⟨s, hs⟩), ?_⟩
      rfl
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl]

theorem exists_sub_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Sh : Finset V) (hS : Submodule.span K (Sh : Set V) = ⊤) (W : Submodule K V) :
    ∃ e : Fin (finrank K (V ⧸ W)) → V, (∀ i, e i ∈ Sh) ∧ Submodule.span K (Set.range e) ⊔ W = ⊤ := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (W.mkQ '' (Sh : Set V))
  have htop : Submodule.span K b = ⊤ := by
    rw [hspan, Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
  have hfin : Finite b := ((Sh.finite_toSet.image _).subset hb).to_subtype
  have := Fintype.ofFinite b
  let bs : Basis b K (V ⧸ W) := Basis.mk hli (by rw [Subtype.range_coe, htop])
  have hcard : Fintype.card b = finrank K (V ⧸ W) := (finrank_eq_card_basis bs).symm
  let eq : Fin (finrank K (V ⧸ W)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ k, ∃ v ∈ (Sh : Set V), W.mkQ v = (eq k : V ⧸ W) := fun k => hb (eq k).2
  choose e he1 he2 using hpre
  refine ⟨e, fun i => he1 i, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (⇑W.mkQ ∘ e) = (Subtype.val : b → V ⧸ W) ∘ eq := by funext k; exact he2 k
  rw [this, Set.range_comp, eq.surjective.range_eq, Set.image_univ, Subtype.range_coe, htop]

end LinAlgQ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem rhoP_eq_finrank (B : WeightFamilies.Prov D) (CR T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    WeightFamilies.rhoP B CR T c j ka = finrank B.KO (B.Cusp j ka ⧸ WeightFamilies.MggK B CR T c j ka) :=
  finrank_quot_eq (B.Mlat j ka) hM (WeightFamilies.MggK B CR T c j ka)

theorem exists_global_family_quotient_bounded {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c be Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) be)
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hbe : be ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    ∃ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
      ({ G0 with rq := WeightFamilies.rhoP B CRm T c j ka, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  have hMtop : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    top_le_iff.mp (hspan ▸ Submodule.span_mono fun x hx => hM (hSh hx))
  have hex := exists_sub_basis Sh hspan (WeightFamilies.MggK B CRm T c j ka)
  rw [← rhoP_eq_finrank B CRm T c j ka hMtop] at hex
  obtain ⟨e, he, hsup⟩ := hex
  exact ⟨fun i => ⟨e i, hM (hSh (he i))⟩, rfl, fun i => hSh (he i), hsup, fun i => (hshort _ (he i)).trans hbe⟩

section Unchanged

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

variable {G0} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la)

end Unchanged

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def ShareRhoT (T rz rq d : ℕ) : Prop := (rz : ℝ) ≤ rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def flipOneThree (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4)
    (max ((2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 * (nW : ℝ) + 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3))

def PageSupp (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (C2 A2 : ℝ) (nW : ℕ) (S : Scal B) (wL : WeightFamilies.Wt D j) :
    Prop :=
  flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r ∧ 3 ≤ DF wL

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound4 (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Prop :=
  ∀ la (ζ : PtsG G la),
    0 ≤ X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ∧ (X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la ((Qf la).y ζ) ≤
        (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal : ℝ) : EReal))

theorem combBound4_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : j < D.R.m) (h : CombBound G S c nus) (Qf : ∀ la, LocalPointData G la) : CombBound4 G Qf S c nus :=
  fun la ζ => (h la ((Qf la).y ζ)).1 hj

def DepthAtM (X : PJ D B P j) (S : Scal B) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal)

theorem depthAtM_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (h : CombBound G S c nus) : DepthAtM X S wL nus :=
  fun la y => (h la y).2 hj

def ConclAtM (large₂ : SizeData₂ D) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  D.R.m ≤ j → DepthAtM X S wL nus →
    Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def PageGd4 (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

theorem pageGd4_iff {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {large₂ : SizeData₂ D} {CG AG Pd : ℝ} :
    PageGd4 X ka large₂ CG AG Pd ↔ PageGd X ka large₂ CG AG Pd := Iff.rfl

def PolyDom4 (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

theorem polyDom4_iff {B : WeightFamilies.Prov D} {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ}
    {ka : WeightFamilies.Wt D j} :
    PolyDom4 D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ↔ PolyDom D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka :=
  Iff.rfl

def Conclusion1OfComb4 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def zAll (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) : Set (Rp X la G.N) :=
  {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
      θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)}

def InContainMR (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) '' (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
    Submodule.span (Kp X la G.N)
      ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T)

def ShareRhoR (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) : Prop :=
  ∀ la, (finrank (Kp X la G.N) ↥(Submodule.span (Kp X la G.N) (zAll G la S T)) : ℝ) ≤
    22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def GrowthConstantBound (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (Gc : ℝ) : Prop :=
  ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), Formalism.MainNotions.WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) po ≤ Gc

def PageGq (large₂ : SizeData₂ D) (Gc Ch Ah : ℝ) : Prop := Gc ≤ WeightFamilies.PPv D large₂ Ch Ah

def GlobalFamilyData.setZQ (G : GlobalFamilyData X ka wL wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
    (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G.N) →₀ ℕ) →₀ B.Cusp j ka) (rq : ℕ) (th : Fin rq → B.Mlat j ka) :
    GlobalFamilyData X ka wL wF :=
  { G with rz := rz, alz := alz, th0 := th0, zc := zc, rq := rq, th := th }

section Tr

variable (G : GlobalFamilyData X ka wL wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
    (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G.N) →₀ ℕ) →₀ B.Cusp j ka) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

def LocalPointData.tr {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : LocalPointData (G.setZQ rz alz th0 zc rq th) la :=
  ⟨Q.y, Q.g0, Q.c⟩

theorem tr_InLiftC {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (Gc Prw : ℝ) (T : ℕ) (h : Q.InLiftC S Gc Prw T) :
    (Q.tr G rz alz th0 zc rq th).InLiftC S Gc Prw T := h

theorem tr_CombBound (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (h : CombBound G S c nus) :
    CombBound (G.setZQ rz alz th0 zc rq th) S c nus := h

end Tr

theorem ShortG.mono {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β β' : ℝ} (h : ShortG X w N β) (hb : β ≤ β') :
    ShortG X w N β' := by
  unfold ShortG at h ⊢
  obtain ⟨Sh, h1, h2, h3⟩ := h
  exact ⟨Sh, h1, h2, fun g hg => (h3 g hg).trans hb⟩

theorem exists_prime (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩⟩

private theorem size_nonneg_lemma (w : WeightFamilies.Wt D j) : 0 ≤ w.size := by
  unfold WeightFamilies.Wt.size
  positivity

theorem shortG_of_scalB {large₂ : SizeData₂ D} {C1 A1 : ℝ} {S : Scal B} {T : ℕ} {Gc : ℝ}
    (hS : ScalB large₂ X C1 A1 S ka wL wF T) (hG : GrowthConstantBound large₂ B Gc) :
    ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) (Gc * (X.wF0 wL wF).size) ∧
      ShortG X ka (X.Thc S.sK ka) (Gc * ka.size) := by
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPL, -, -, hs0, hsK⟩ := hS
  have hG' := hG
  unfold GrowthConstantBound at hG'
  have hle : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG' po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  exact ⟨ShortG.mono hs0 (mul_le_mul_of_nonneg_right hle (size_nonneg_lemma _)),
    ShortG.mono hsK (mul_le_mul_of_nonneg_right hle (size_nonneg_lemma _))⟩

theorem inContainM_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (hM : InContainMR G la S CRm T c) (hZ : InContainZ G la S T) : InContainM G la CRm T c := by
  refine le_trans hM ?_
  rw [Submodule.span_le]
  rintro v (hv | hv)
  · exact Submodule.subset_span (Or.inl hv)
  · have h1 : v ∈ Submodule.span (Kp X la G.N) (Set.range (zK G la)) :=
      hZ (Submodule.subset_span hv)
    exact Submodule.span_mono Set.subset_union_right h1

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Base

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

theorem bcV_mem_Vw {x : X.Vl la} (hx : x ∈ T0.WL X ka la) : bcV X la N x ∈ Vw X la N ka := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨F', _, rfl⟩, rfl⟩ := hx
    exact emb_mem_Vw X la N ka F'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul (Kp X la N) a]
    exact Submodule.smul_mem _ _ hx

def jW : ↥(T0.WL X ka la) →ₗ[X.Kl la] ↥(Vw X la N ka) :=
  ((bcV X la N).toLinearMap.domRestrict (T0.WL X ka la)).codRestrict ((Vw X la N ka).restrictScalars (X.Kl la))
    fun x => bcV_mem_Vw X la N ka x.2

def M1 : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.MW X ka la : Set ↥(T0.WL X ka la)))

def Th1 (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.ThW X S ka wL wF T la : Set ↥(T0.WL X ka la)))

def MggO (B : WeightFamilies.Prov D) (CRm T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j ka) :=
  B.Mlat j ka ⊓ (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)

def MggW (CRm T c : ℝ) : Submodule (X.Ol la) ↥(T0.WL X ka la) :=
  T0.inW X ka la (X.loc la (X.emb ka (MggO B CRm T c j ka)))

def toW (F : B.Mlat j ka) : ↥(T0.WL X ka la) :=
  ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩⟩

end Base

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def sectionMonomialGenerators : Set ↥(Vw X la G.N (addL wF wL T)) :=
  {f | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
      (f : Rp X la G.N) = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))}

def N1 : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (sectionMonomialGenerators G la)

def Zg : Set ↥(Vw X la G.N (addL wF wL T)) := {f | ∃ k : Fin G.rz, (f : Rp X la G.N) = zK G la k}

def Zl : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (Zg G la)

def ZK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Kp X la G.N) (Zg G la)

def NovK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  Submodule.span (Kp X la G.N) ((N1 G la ⊔ Zl G la : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T))) :
    Set ↥(Vw X la G.N (addL wF wL T)))

def Zm : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  M1 X la G.N (addL wF wL T) ⊓ (ZK G la).restrictScalars (Op X la G.N)

def Np (e : ℕ) : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  ((M1 X la G.N (addL wF wL T)).map ((unifO X la G.N ^ e) •
      (LinearMap.id : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] ↥(Vw X la G.N (addL wF wL T)))) ⊓
    (NovK G la).restrictScalars (Op X la G.N)) ⊔ N1 G la ⊔ Zm G la

def rhoO : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  (rhoK X la G.w wF (a0 D j T) T).restrictScalars (Op X la G.N)

def rhoN (e : ℕ) : ↥(Np G la e) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  rhoO G la ∘ₗ (Np G la e).subtype

theorem reducedGenerators_eq_map : firstLength_le_prime_bound G la T = (N1 G la).map (rhoO G la) := by
  unfold firstLength_le_prime_bound N1
  rw [Submodule.map_span]
  rfl

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end
