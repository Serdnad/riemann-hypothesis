module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle079
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle085
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardOfInjective
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle216
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realization_family_normal_operators : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t, ∃ h, IsOpsX R t h ∧ NormalFam (Good R t) h) ∧ ∀ i t, ∃ h, IsOpsV R i t h ∧ NormalFam (Good R t) h := by
  first | exact @GlobalTheory.DefiniteOps.definite_ops | exact GlobalTheory.DefiniteOps.definite_ops | (intros; apply GlobalTheory.DefiniteOps.definite_ops <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

noncomputable section

namespace GlobalTheory.JetOpWeylLat

open GlobalTheory.JetPoint GlobalTheory.LiftTypePrime Formalism.GradedWeylDivisibility

section Expand

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_mul_monomial (J : (DVar ι a b →₀ ℕ) → K) (P : Pol K ι b) (m : DVar ι a b →₀ ℕ) :
    jetLin J (rename Sum.inl P * rename Sum.inr (monomial m (1 : K))) = J m • P := by
  induction P using MvPolynomial.induction_on' with
  | monomial p c =>
    rw [rename_monomial, rename_monomial, monomial_mul, mul_one, jetLin, constr_monomial]
    have h1 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = p := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
    have h2 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
    rw [h1, h2, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]
  | add p q hp hq => rw [map_add (f := _), add_mul, map_add (f := _), hp, hq, smul_add]

def joinExp (α : ι → (Fin b × Fin a →₀ ℕ)) : DVar ι a b →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k => α k.1 k.2

theorem subD_ten [DecidableEq ι] (h : a ≤ b) (F : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (F τ)).support,
        rename Sum.inl (ten fun τ => map (Int.castRingHom K) ((subGen h (F τ)).coeff (α τ))) *
          rename Sum.inr (monomial (joinExp α) (1 : K)) := by
  have e1 : subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∏ τ, aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
        (X (Sum.inl (τ, β, Fin.castLE h v.2)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) *
          X (Sum.inr (τ, β, v.1))) (F τ) := by
    unfold subD ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [aeval_rename]
    refine (aeval_map_algebraMap K _ (F τ)).trans ?_
    congr 2
    funext v
    have hv : (v.2 : ℕ) < b := lt_of_lt_of_le v.2.2 h
    simp only [Function.comp_apply, dif_pos hv]
    rfl
  rw [e1]
  refine (Finset.prod_congr rfl fun τ _ => aeval_subGen h
    (fun v : Fin b × Fin a => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K))
    (fun v : Fin b × Fin b => X (Sum.inl (τ, v))) (F τ)).trans ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  · unfold ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [rename_rename, rename_eq_aeval]
    exact (aeval_map_algebraMap K _ _).symm
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine (Finsupp.prod_fintype (α τ)
      (fun v e => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) ^ e) (by simp)).trans ?_
    simp [joinExp]

theorem jetMap_ten [DecidableEq ι] (h : a ≤ b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (f : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).support,
        J (joinExp α) • ten fun τ =>
          map (Int.castRingHom K) ((subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).coeff (α τ)) := by
  have e : (ten fun τ => map (Int.castRingHom K) (f τ)) * ∏ τ, frDet K a τ ^ n τ =
      ten fun τ => map (Int.castRingHom K) (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ) := by
    rw [← GlobalTheory.WeylMinorDual.ten_gdet]
    simp only [ten, map_mul, map_pow, GlobalTheory.WeylMinorDual.map_gdet, Finset.prod_mul_distrib]
  change jetLin J (subD K ι a b (_ * _)) = _

  rw [e, subD_ten h, map_sum]
  exact Finset.sum_congr rfl fun α _ => jetLin_mul_monomial _ _ _

end Expand

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem toK_map_int {σ : Type} (f : MvPolynomial σ ℤ) :
    toK K σ (map (Int.castRingHom (𝓞 K)) f) = map (Int.castRingHom K) f := by
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 1

theorem ten_mem_delStd (lam : ι → DomWeight a) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) : (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ delStd K lam :=
  Submodule.subset_span ⟨_, fun τ => ⟨_, GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) _ _ _ (hf τ),
    toK_map_int _⟩, rfl⟩

theorem delStd_le_span (lam : ι → DomWeight a) :
    delStd K lam ≤ Submodule.span (𝓞 K) {P | ∃ f : ι → MvPolynomial (Fin a × Fin a) ℤ,
      (∀ τ, f τ ∈ delSq ℤ a (lam τ)) ∧ P = ten fun τ => map (Int.castRingHom K) (f τ)} := by
  have h : ∀ τ, (delSq (𝓞 K) a (lam τ)).map (toK K _) = Submodule.span (𝓞 K) (Set.range fun u =>
      map (Int.castRingHom K) (applyWord ℤ u (hw ℤ (le_refl a) (lam τ).natW))) := fun τ => by
    rw [delSq, weyl, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext u
    rw [← toK_map_int, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    rfl
  unfold delStd
  simp only [h]
  rw [GlobalTheory.WeylMinorDual.tensorLat_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨_, fun τ => Submodule.subset_span ⟨u τ, rfl⟩, rfl⟩

theorem mem_localization_weylLattice_iff (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a)
    {M : ι → Submodule (𝓞 K) (Fin a → K)} (hM : LatWithBasis w M 1) (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔ (F : Pol K ι a) ∈ localization₂ w.asIdeal (delStd K lam) := by
  have h1 : F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔
      (F : Pol K ι a) ∈ localization₂ w.asIdeal (delP lam fun τ => dualFr (M τ)) := Iff.rfl
  have h2 := (GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam (fun τ => dualFr (M τ))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.HAtBasis.isLattice_of_basisAt w (hM τ).1 (hM τ).2)) w
    (fun τ => inside₂ K a ((1 : ι → GL (Fin a) K) τ))
    (fun τ => GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hM τ).1 (hM τ).2)).2
  rw [h1, h2, GlobalTheory.TransLoc.mem_map_actP, GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul, blockAct_one,
    AlgHom.id_apply]

theorem smul_mem_localizationAt_of_valuation (w : HeightOneSpectrum (𝓞 K)) {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    [IsScalarTower (𝓞 K) K Z] {T : Submodule (𝓞 K) Z} {x : K}
    (hx : w.valuation K x ≤ 1) {P : Z} (hP : P ∈ T) : x • P ∈ localization₂ w.asIdeal T := by
  obtain ⟨r, ⟨d, hd⟩, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have h' : algebraMap (𝓞 K) K d * x = algebraMap (𝓞 K) K r := (mul_comm _ _).trans h
  have e : d • x • P = r • P := by
    rw [← algebraMap_smul K d (x • P), smul_smul, h', algebraMap_smul]
  exact ⟨d, hd, e ▸ T.smul_mem r hP⟩

theorem jetMap_ten_mem (w : HeightOneSpectrum (𝓞 K)) {hab : a < b} {lam : ι → DomWeight a} {lam' : ι → DomWeight b}
    {s s' : ι → ℤ} {n : ι → ℕ} (hw : WtCompat hab lam lam' s s' n) {c : K} {J : (DVar ι a b →₀ ℕ) → K}
    (hJ : ∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) :
    c • jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ localization₂ w.asIdeal (delStd K lam') := by
  classical
  have hF : ∀ τ, f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ ∈ weyl ℤ a a le_rfl fun r => (lam τ).natW r + n τ := fun τ => by
    rw [GlobalTheory.WeylMinorDual.weyl_add]
    exact ⟨f τ, hf τ, rfl⟩
  have hν : ∀ τ (j : Fin b), (lam' τ).natW j = if h : (j : ℕ) < a then (lam τ).natW ⟨j, h⟩ + n τ else 0 := by
    intro τ j
    have e0 := GlobalTheory.WeylMinorDual.natW_cast (lam' τ) j
    have e5 := detShift_eq hw τ
    split_ifs with h
    · have e1 : (lam' τ).w j + s τ = _ := hw.1 τ ⟨j, h⟩
      have e2 := GlobalTheory.WeylMinorDual.natW_cast (lam τ) ⟨j, h⟩
      have e3 := hw.2.2 τ
      omega
    · have e1 := hw.2.1 τ j (not_lt.1 h)
      omega
  rw [jetMap_ten hab.le, Finset.smul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [smul_smul]
  refine smul_mem_localizationAt_of_valuation w (hJ _ fun τ => ?_)
    (ten_mem_delStd lam' fun τ => coeff_subGen_mem hab.le (natW_anti _) (hν τ) (hF τ) _)
  have h1 := subGen_isHomogeneous hab.le (isHomogeneous_of_mem_weyl
    (fun _ _ h => Nat.add_le_add_right (natW_anti _ h) _) (hF τ)) (mem_support_iff.1 (Fintype.mem_piFinset.1 hα τ))
  have h2 : (∑ β : Fin b, ∑ γ : Fin a, joinExp α (τ, β, γ)) = ∑ r, ((lam τ).natW r + n τ) := by
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
    simp [joinExp]
  rw [h2, Nat.cast_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.cast_add, GlobalTheory.WeylMinorDual.natW_cast, hw.2.2 τ]
  ring

theorem jetOpWeyl : GlobalTheory.ColPeriod.JetOpWeyl := by
  intro K _ _ w ι _ a b hab lam lam' s s' n hw M MW _ _ hM hMW c J hJ F hF
  have hmem : jetMap J n (F : Pol K ι a) ∈ Formalism.L2.DIV.VV K lam' :=
    jetMap_mem hab.le n _ _ (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2) J
  rw [mem_localization_weylLattice_iff w lam hM] at hF
  rw [mem_localization_weylLattice_iff w lam' hMW, Submodule.coe_smul, coe_jetOp _ _ _ _ _ hmem]
  have key : delStd K lam ≤ (localization₂ w.asIdeal (delStd K lam')).comap ((c • jetMap J n).restrictScalars (𝓞 K)) := by
    refine (delStd_le_span lam).trans (Submodule.span_le.2 ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact jetMap_ten_mem w hw hJ hf
  obtain ⟨t, ht, hF⟩ := hF
  obtain ⟨u, hu, h⟩ := key hF
  refine ⟨u * t, mul_mem hu ht, ?_⟩
  rw [map_smul] at h
  rw [mul_smul]
  exact h

end GlobalTheory.JetOpWeylLat
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriod.Scal

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)

variable {X : Fields} {Pr : Primes X}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (GlobalTheory.ColPeriod.mem_divs h)

theorem g_notMem_of_vGs (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) (h' : P ∉ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  have h2 : ∃ k, P ∈ Pr.vG k := by
    rcases Finset.mem_union.1 h with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  obtain ⟨k, hk⟩ := h2
  have hne : Pr.g i ≠ Pr.g k := by
    have h0 := hPr.g_ne
    fin_cases i <;> fin_cases k
    · exact absurd hk h'
    · exact h0
    · exact h0.symm
    · exact absurd hk h'
  exact natCast_notMem_of_ne (hPr.g_prime i) (hPr.g_prime k) hne P (g_mem_of_vG hPr hk)

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem g_notMem_sel (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ rowSG Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  rw [← hPr.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), by rw [under_conjP hX, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hsel v⟩

theorem val_locChar_unit {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (cq : K) (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (ha : P.valuation E a = 1) :
    w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  have hu := GlobalTheory.LocCharVal.isUnit_redP P _ ha
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  rw [GlobalTheory.LastSteps.locChar_unit _ _ hu, LocE.unitV, dite_eq_left hu]
  exact GlobalTheory.CharVal.unit_of_finOrder (MonoidHom.isOfFinOrder ψ (isOfFinOrder_of_finite _))

theorem val_locChar {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) {cq : K} (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hc : w.valuation K cq = 1) {a : E} (ha : a ≠ 0) : w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul E K P (qOf P) cq ψ a
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hq) ha
  rw [e, map_mul, map_zpow₀, hc, GlobalTheory.CharVal.unit_of_finOrder hζ, one_zpow, one_mul]

end GlobalTheory.ColPeriod.Scal

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker Scal

theorem scalarUnit_of (hL : LevelPrimes) (hH : HeckeUnit) (hT : TwistUnit) : ScalarUnit := by
  intro X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hS ht hOk i w hw j hj
  have hH' := hH X Pr R.m Ch G.σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (G.mu0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.g i) w
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      w.valuation X.K (Ch.muVal ⟨j, hj⟩ P : X.K) = 1 := fun P hP =>
    hH' P (hPr.g_prime i) hw (hP i) (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1 := by
    intro P hPi
    have hq := (hT X.F X.E X.K S mu P.1 w).2
    obtain ⟨hd, hn⟩ := hL X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · have h1 := hOk.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have h3 := hH' P.1 (hPr.g_prime i) hw (g_notMem_of_vGs hPr hP hPi) _ _ h2
      rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hOk.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        hq, hval _ hg]
      simp
  refine ⟨h1, fun n N fr _ hN hfr => ?_⟩
  have h2 : w.valuation X.K (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N) = 1 := by
    unfold muOff
    refine finprod_induction (fun x => w.valuation X.K x = 1) (map_one _)
      (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · exact map_one _
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dite_eq_left hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hval _ (g_notMem_sel hX hPr hsel hv),
        (hT X.F X.E X.K S mu _ w).1]
      simp
  rw [muInvDet, map_mul, h2, one_mul, map_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  by_cases hP : P.1 ∈ Pr.vG i
  · refine val_locChar_unit w P.1 _ _ ?_
    rw [LinearEquiv.coe_det]
    refine GlobalTheory.StdReps.val_det_eq fun x => ?_
    rw [← hfr P x, hN P.1 (g_mem_of_vG hPr hP)]
  · exact val_locChar w P.1 _ (hL X Pr sel S mu hX hPr hsel P).1.2 (h1 P hP) (Units.ne_zero _)

end GlobalTheory.ColPeriod
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  intro p _ X D pos Kc _ _ _ fd c j La' d R hR
  classical
  let blk : Var (X.Pj (j + 1)) → Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) := fun y => ⟨y.1, y.2.1⟩
  let E : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) → Kc := fun b => if IsOddPos b.2 then 1 else c
  have hf : ∀ y, GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') y =
      MvPolynomial.C (E (blk y)) * GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.mk Kc fd j La') y := by
    intro y
    unfold GlobalTheory.FrameB.frF GlobalTheory.FrameB.wV
    simp only [E, blk]
    split_ifs with h1 h2 h2
    · simp only [MvPolynomial.C_1, one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp only [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, Finset.mul_sum, mul_assoc]
  have hm : ∀ m ∈ R.support, (∏ y, E (blk y) ^ m y) = ∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ := by
    intro m hmR
    rw [← Finset.prod_fiberwise Finset.univ blk, ← (posJ X D pos (j + 1)).prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hpb : pos.symm (posJ X D pos (j + 1) b) = b := pos.symm_apply_apply b
    have h2 : ∏ y ∈ Finset.univ.filter (fun y => blk y = b), E (blk y) ^ m y =
        E b ^ (∑ y ∈ Finset.univ.filter (fun y => blk y = b), m y) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2]
    rw [h2, hpb]
    simp only [E]
    split_ifs with h1 h3 h3
    · exact one_pow _
    · exact absurd h1 h3
    · exact absurd h3 h1
    · have hd := hR m hmR (posJ X D pos (j + 1) b) (by rw [hpb]; exact h1)
      rw [Equiv.symm_apply_apply, ← Finset.sum_filter] at hd
      rw [← hd, ← Nat.cast_sum, zpow_natCast]
  unfold GlobalTheory.FrameB.tau0
  conv_lhs => rw [R.as_sum]
  conv_rhs => rw [R.as_sum]

  simp only [map_sum, Finset.smul_sum, MvPolynomial.aeval_monomial]
  refine Finset.sum_congr rfl fun m hmR => ?_
  rw [← hm m hmR]
  simp only [hf]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.isAutomorphicOfWeight_of_nonzero_fixed_finPart_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := by
  first | (exact @GlobalTheory.Cong.ofType_of_finPart_fixed) | (exact GlobalTheory.Cong.ofType_of_finPart_fixed) | (intros; apply GlobalTheory.Cong.ofType_of_finPart_fixed  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.curveLattice_sigmaTwo_algebraic_of_invariants_algebraic : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  first | exact @GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | exact GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg | (intros; apply GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg <;> assumption)
end
