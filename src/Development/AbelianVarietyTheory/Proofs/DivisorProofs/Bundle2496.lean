module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle863
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle862
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle005
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical



noncomputable section

namespace GlobalTheory.QHalfLat

variable {D : D7}
open scoped Matrix

theorem frMapAdj_gen {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} {α : Af D.host.F}
    (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (hca : toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hca hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z

    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
    ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m

    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, GlobalTheory.ConjHalfInt.cF_eToEAf,
    ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fS hs) (GlobalTheory.ConjHalfInt.pair_row_int hT fT ht)

theorem isIntM_adj_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {c : AE D} (hc : ∀ a ∈ D.host.AA, toEAf D (c * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {x : WO S T} (hx : IsHalf c x)
    (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapAdj S T βS βT x) := by
  have hx' : c • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (c • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact frMapAdj_gen hS hT fS fT hα' (hc a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem placesOK_of {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q)
    (hQ : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) : GlobalTheory.ExportSeries.PlacesOK Q ∅ := by
  refine ⟨⟨Q, subset_rfl, Finset.empty_subset _, (⟨e, he⟩ : ∃ e : AE D, IsIdemSum e Q)⟩, Finset.disjoint_empty_right _, ?_⟩
  rintro PP (hPP | hPP) PP' hPP'
  · rcases hPP' with rfl | hc
    · exact GlobalTheory.HalfCompare.primeToAA_of_not_mem (hQ _ hPP)
    · rw [(GlobalTheory.IdemSupport.isConjPl_iff PP PP').1 hc]
      refine GlobalTheory.HalfCompare.primeToAA_of_not_mem ?_
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact hQ PP hPP
  · simp at hPP

end GlobalTheory.QHalfLat


open GlobalTheory.QHalfLat in
theorem GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQt eQ he t ht
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, ht0⟩ := hQt
  have hbad : ∀ PP ∈ Q, ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t0 PP (ht0 hPP)
  have hP := placesOK_of he hbad
  have hid : GlobalTheory.ExportSeries.idem Q = eQ :=
    GlobalTheory.DatumFourier.idemSum_unique (Vc D i) he (show GlobalTheory.ExportSeries.SplitSet Q from ⟨eQ, he⟩).isIdemSum
  have ht' : IsHalf (cA D (GlobalTheory.ExportSeries.idem Q)) t := by rw [hid]; exact ht
  constructor
  · intro hi
    exact GlobalTheory.ConjLatAdj.mem_latO_of_adj_int hSV hSW hFV hFW hP ht' hi
  · intro hl
    exact isIntM_adj_of_mem hSV hSW hFV hFW (fun a ha => GlobalTheory.ConjHalfInt.toEAf_cA_idem_mul_mem hP ha) ht' hl
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem detPol_mem_dualWeyl_one (R : Type) [CommRing R] (n : ℕ) :
    detPol R n ∈ dualWeyl R n n (fun _ => 1) := by
  have h := Formalism.GradedWeylDivisibility.bidetMem R n n 1 (fun _ => n) (fun _ => le_refl n) (fun _ => id)
  have hb : bideterminant R (r := n) (n := n) (fun _ : Fin 1 => n) (fun _ => le_refl n) (fun _ => id) = detPol R n := by
    simp [bideterminant, initMinor, detPol]
  have hs : shapeDeg (n := n) (fun _ : Fin 1 => n) = fun _ => 1 := by
    funext t
    simp [shapeDeg, t.isLt]
  rw [hb, hs] at h
  exact h

theorem detPol_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  intro R _ n k ν f hf
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := (Formalism.GradedWeylDivisibility.dualWeylMul R n n (fun _ => 1) (fun a => ν a + k) (detPol R n) (detPol R n ^ k * f)).1
      (detPol_mem_dualWeyl_one R n) ih
    have he : ((fun _ => 1) + fun a => ν a + k) = fun a : Fin n => ν a + (k + 1) := by
      funext a; simp only [Pi.add_apply]; omega
    rw [he, ← mul_assoc, ← pow_succ'] at h
    exact h

end GlobalTheory.FrameRead
end

section

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem norm_map_le_one_of_isIntegral_int {F C : Type} [CommRing F] [NormedField C] [IsUltrametricDist C] (f : F →+* C) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (f x) := hx.map f.toIntAlgHom
  have := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hy.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_le_one_iff_integral_at : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  intro K _ _ l _ w e0 hw x
  constructor
  · intro hx
    obtain ⟨n, d, h | h⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact h⟩
    · by_cases hn : n ∈ w.asIdeal
      · exfalso
        refine d.2 ((hw d).2 ?_)
        have h1 : ‖e0 ((d : 𝓞 K) : K)‖ = ‖e0 x‖ * ‖e0 (n : K)‖ := by
          have : ((d : 𝓞 K) : K) = x * (n : K) := h.symm
          rw [this, map_mul, norm_mul]
        rw [h1]
        have h2 : ‖e0 (n : K)‖ < 1 := (hw n).1 hn
        calc ‖e0 x‖ * ‖e0 (n : K)‖ ≤ 1 * ‖e0 (n : K)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact h2
      · exact ⟨n, hn, d, by rw [mul_comm]; exact h⟩
  · rintro ⟨s, hs, r, hr⟩
    have hs1 : 1 ≤ ‖e0 (s : K)‖ := by
      by_contra h
      exact hs ((hw s).2 (lt_of_not_ge h))
    have hr1 : ‖e0 (r : K)‖ ≤ 1 := norm_map_le_one_of_isIntegral_int e0 r.isIntegral_coe
    have h1 : ‖e0 (s : K)‖ * ‖e0 x‖ ≤ 1 := by rw [← norm_mul, ← map_mul, hr]; exact hr1
    nlinarith [norm_nonneg (e0 x)]

end GlobalTheory.FrameRead
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem exists_gl_preimage {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) (hφ : Function.Injective φ) {n : ℕ}
    (u : GL (Fin n) C) (h : ∀ a b, u.val a b ∈ Set.range φ ∧ (u⁻¹).val a b ∈ Set.range φ) :
    ∃ u0 : GL (Fin n) O, Matrix.GeneralLinearGroup.map φ u0 = u := by
  choose M hM using fun a b => (h a b).1
  choose M' hM' using fun a b => (h a b).2
  have e1 : φ.mapMatrix (Matrix.of M) = u.val := by ext a b; simp [hM]
  have e2 : φ.mapMatrix (Matrix.of M') = (u⁻¹).val := by ext a b; simp [hM']
  have inj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) C) := fun A B hAB => by
    ext a b; exact hφ (congrFun (congrFun hAB a) b)
  have h1 : Matrix.of M * Matrix.of M' = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have h2 : Matrix.of M' * Matrix.of M = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  refine ⟨⟨Matrix.of M, Matrix.of M', h1, h2⟩, Units.ext ?_⟩
  exact e1

theorem det_map_gl {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {n : ℕ} (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem lamG_mem_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  intro l _ ι _ _ n lamW c F hinj hlam u hu z
  choose u0 hu0 using fun τ => exists_gl_preimage F.emb hinj (u τ) (hu τ)
  have hu' : u = fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ) := funext fun τ => (hu0 τ).symm
  subst hu'
  have hs : ((∏ τ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (u0 τ)) ^ c τ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      F.emb ((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) := by
    simp only [det_map_gl, ← map_zpow, ← map_prod]
    rfl
  have key : ∀ x, lamG (PadicAlgCl l) n lamW c (fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ)) (GlobalTheory.LatBC.bc F.emb n lamW x) =
      GlobalTheory.LatBC.bc F.emb n lamW (((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) • grp F.O n lamW u0 x) := by
    intro x
    rw [lamG_apply, hs, ← GlobalTheory.LatBC.bc_grp, LinearMap.map_smulₛₗ]
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 hz
    exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨_, (key x).symm⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.LatBC.latD_iff F lamW hlam _).1 hz
    refine (GlobalTheory.LatBC.latD_iff F lamW hlam _).2 ⟨_, ?_, (key x).symm⟩
    exact Submodule.smul_mem _ _ (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta F.O ι (fun _ => n) (fun _ => n) (fun _ => le_rfl)
      (fun τ => res n (lamW τ)) u0 x hx)

end GlobalTheory.FrameRead
end
end

section

set_option autoImplicit false

noncomputable section

open Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead

namespace GlobalTheory.WeylShift

variable (R : Type) [CommRing R]

theorem rowGen_detPol (n : ℕ) (a b : Fin n) :
    rowGen R a b (detPol R n) =
      (1 + (if a = b then Polynomial.X else 0)) * Polynomial.C (detPol R n) := by
  have hC : (Polynomial.C (detPol R n) : Polynomial (MvPolynomial (Fin n × Fin n) R)) =
      Matrix.det (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) := by
    unfold detPol
    rw [RingHom.map_det]
    rfl
  rw [hC]
  set A := (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) with hA
  have h1 : rowGen R a b (detPol R n) =
      Matrix.det (A.updateRow b (A b + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • A a)) := by
    unfold detPol
    rw [AlgHom.map_det]
    congr 1
    ext1 p s
    by_cases hp : p = b
    · subst hp
      simp [rowGen, hA]
    · simp [rowGen, hA, hp, Matrix.updateRow_ne hp]
  rw [h1]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, if_pos rfl]
    ring
  · rw [Matrix.det_updateRow_add_smul_self A (Ne.symm hab), if_neg hab]
    ring

theorem rowDiv_det_mul_zero (n : ℕ) (a b : Fin n) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b 0 (detPol R n * g) = detPol R n * rowDiv R a b 0 g := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs <;> simp [add_mul, mul_assoc]

theorem rowDiv_det_mul_succ (n : ℕ) (a b : Fin n) (j : ℕ) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b (j + 1) (detPol R n * g) =
      detPol R n * rowDiv R a b (j + 1) g + (if a = b then detPol R n * rowDiv R a b j g else 0) := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs
  · rw [add_mul, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  · simp

theorem lpMinor_full (n s : ℕ) (h : s = n) (h1 h2 : s ≤ n) : lpMinor R s h1 h2 = detPol R n := by
  subst h
  rfl

theorem hw_add_one (n : ℕ) (ν : Fin n → ℕ) :
    hw R (le_refl n) (fun a => ν a + 1) = detPol R n * hw R (le_refl n) ν := by
  cases n with
  | zero => simp [hw, detPol]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h1 : ∀ s : Fin m, (ν s.castSucc + 1) - nuNext (fun a => ν a + 1) s.castSucc
        = ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs : s.castSucc.val + 1 < m + 1 := by have := s.2; simp
      simp only [nuNext, dif_pos hs]
      omega
    have h2 : ∀ μ : Fin (m + 1) → ℕ, nuNext μ (Fin.last m) = 0 := by
      intro μ
      simp [nuNext]
    simp only [h1, h2, Nat.sub_zero]
    rw [lpMinor_full R (m + 1) ((Fin.last m).val + 1) (by simp)]
    ring

theorem mem_weyl_add_one (n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + 1) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n * g := by
  have key : weyl R n n le_rfl (fun a => ν a + 1) =
      (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      induction w with
      | nil =>
        exact ⟨hw R le_rfl ν, Submodule.subset_span ⟨[], rfl⟩, (hw_add_one R n ν).symm⟩
      | cons x w ih =>
        obtain ⟨g, hg, hge⟩ := ih
        obtain ⟨a, b, j⟩ := x
        have he : applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) =
            rowDiv R a b j (detPol R n * g) := by
          have : detPol R n * g = applyWord R w (hw R le_rfl fun a => ν a + 1) := hge
          rw [this]; rfl
        show applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) ∈
          (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n))
        rw [he]
        have hm : ∀ i, detPol R n * rowDiv R a b i g ∈
            (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := fun i =>
          ⟨_, weylModuleRowDividedPowerStable R n n le_rfl ν a b i g hg, rfl⟩
        cases j with
        | zero => rw [rowDiv_det_mul_zero]; exact hm 0
        | succ j =>
          rw [rowDiv_det_mul_succ]
          refine Submodule.add_mem _ (hm _) ?_
          split_ifs
          · exact hm _
          · exact Submodule.zero_mem _
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      show detPol R n * applyWord R w (hw R le_rfl ν) ∈ weyl R n n le_rfl (fun a => ν a + 1)
      induction w with
      | nil =>
        exact Submodule.subset_span ⟨[], hw_add_one R n ν⟩
      | cons x w ih =>
        obtain ⟨a, b, j⟩ := x
        show detPol R n * rowDiv R a b j (applyWord R w (hw R le_rfl ν)) ∈ _
        generalize applyWord R w (hw R le_rfl ν) = g at ih ⊢
        have hm : ∀ i, rowDiv R a b i (detPol R n * g) ∈ weyl R n n le_rfl (fun a => ν a + 1) := fun i =>
          weylModuleRowDividedPowerStable R n n le_rfl _ a b i _ ih
        induction j with
        | zero => rw [← rowDiv_det_mul_zero]; exact hm 0
        | succ j ihj =>
          have h := hm (j + 1)
          rw [rowDiv_det_mul_succ] at h
          refine (Submodule.add_mem_iff_left _ ?_).1 h
          split_ifs
          · exact ihj
          · exact Submodule.zero_mem _
  rw [key, Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

theorem mem_weyl_add (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + k) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n ^ k * g := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have h := mem_weyl_add_one R n (fun a => ν a + k) f
    refine Iff.trans h ?_
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := (ih g).1 hg
      exact ⟨g', hg', by ring⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (ih _).2 ⟨g, hg, rfl⟩, by ring⟩

end GlobalTheory.WeylShift
end
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



theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ t : WO (Vc D i) (Wc D i), IsHalf (cA D eQ) t → (IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (t)) ↔ t ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | exact GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP | (intros; apply GlobalTheory.QHalfLat.isIntM_adj_iff_mem_latP <;> assumption)

end
end
