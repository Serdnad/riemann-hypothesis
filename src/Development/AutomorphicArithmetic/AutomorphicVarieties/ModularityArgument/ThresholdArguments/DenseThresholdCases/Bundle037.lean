module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.HeckeIdealEnd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Adelise
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolRep
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle027
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
open UpperTheory.V.Sd in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.V.Z.Bc.upCyc_of_alt (hA : _root_.UpperTheory.V.Af.Hypotheses') (cyc : UpperTheory.V.Z.Bc.CycC) : UpperTheory.V.Sd.UpCyc := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hp n hn r hr ⟨π, hreg, hatt⟩ hirr
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have key : (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨
      ∃ P : CuspSub E n, (∀ τ m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧ WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := by
    rcases (cyc F E hp inferInstance n hn).1 _ _ (Or.inl ⟨inferInstance, π, rfl, rfl⟩)
      (fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, hreg τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
    · exact Or.inl h1
    · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
      · exact Or.inr ⟨P, hi, hw⟩
      · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
        exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))
  rcases key with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hA F Ω l ι n r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ n r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ n _).2.1 hirr, ?_⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
namespace UpperTheory.V.Sd.EG
section Norm
variable {l : ℕ} [hl : Fact l.Prime]
end Norm
private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero (ordCompl[r] N) := ⟨(Nat.ordCompl_pos r (NeZero.ne N)).ne'⟩
  have hcop : (ordCompl[r] N).Coprime r := (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
  have hone : ∀ ζ : Ω, ζ ^ ordCompl[r] N = 1 →
      ζ ^ ((1 : (ZMod (ordCompl[r] N))ˣ) : ZMod (ordCompl[r] N)).val = ζ := fun ζ hζ => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  obtain ⟨w, hw⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r) (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA w
  refine ⟨σ, hσ, (Chr.clsFacts ℚ Ω N).2.2.1 σ u ?_⟩
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨fun ζ hζ => ?_, ?_⟩
  · rw [MonoidHom.mem_ker.1 hu, hone ζ hζ]
    exact (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA _ hcop ζ hζ).2 σ hσ
  · have hc : cyclotomicCharacter Ω r σ.toRingEquiv = w := hσw
    rw [hc, hw]
section Gal
variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem ram {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (f : ℂ →+* Qbar l) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N) {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) :
    ¬ Ine (F := ℚ) A ≤ (Chr.dirG ℚ Ω (χ.ringHomComp f)).ker := fun hall => by
  have hft : χ.FactorsThrough (ordCompl[p] N) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.ordCompl_dvd N p)).2 fun u hu => ?_
    obtain ⟨σ, hσ, rfl⟩ := primRam_lift Ω N p hp A hA u hu
    have h1 := congrArg Units.val (MonoidHom.mem_ker.1 (hall hσ))
    refine MonoidHom.mem_ker.2 (Units.ext (f.injective ?_))
    rw [Units.val_one, map_one]
    exact h1
  have hd : χ.conductor ≤ ordCompl[p] N := Nat.sInf_le hft
  rw [hχ] at hd
  have := Nat.div_lt_self (NeZero.pos N) (Nat.one_lt_pow (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne' hp.one_lt)
  omega
theorem exists_ordinary_form_trace_near_one_add_cyc (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) {k N : ℕ} [NeZero N] (hk : 3 ≤ k) (hN : ¬ l ∣ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (g : Eigenform k N χ)
    (hg : ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)))‖ < 1)
    {ψ : G ℚ Ω →* (Qbar l)ˣ} (hm : Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) = ψ) :
    ∃ c π r, OrdForm ι ψ⁻¹ (1 - (k : ℤ)) c (fun _ => ![0, 1 - (k : ℤ)]) (fun _ => 1) π r ∧
      ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + (cycBar ℚ Ω l ^ (k - 1) * ψ) s)‖ < 1 := by
  classical
  obtain ⟨ω, φ, hω, hval, hφ, hcu⟩ := adelise k N (by omega) χ g
  obtain ⟨π, hreg, ⟨χ', hpol⟩, hinf, hU, hsat⟩ := _root_.UpperTheory.V.Sd.holRep_alt P ℚ k (by omega) _ ω hω φ _ hφ hcu
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems ℚ Ω l ι 2 one_le_two π χ' hreg hpol
  have hlN : l * N ≠ 0 := mul_ne_zero hl.out.ne_zero (NeZero.ne N)
  set c : Pl ℚ → ℕ := fun w => N.factorization (normV w) with hc
  have hc0 : ∀ w, c w = 0 ↔ ¬ normV w ∣ N := fun w => by
    simp [hc, Nat.factorization_eq_zero_iff, normV_prime w, (normV_prime w).ne_one, NeZero.ne N]
  set D : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (k - 1) * ψ with hD
  have hDv : ∀ s, (D s : Qbar l) = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom) s := fun s => by
    rw [hD, ← hm]; simp
  have hDc : Continuous fun s => (D s : Qbar l) := by
    simp only [hDv]
    exact (cyc_cont.pow _).mul (dirG_cont _)
  have c1 : Continuous fun s : G ℚ Ω => (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hG.cont.comp continuous_inv)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    ((Filter.eventually_cofinite.1 hatt.2).union (fin_dvd hlN))
  have hall : ∀ s, ‖(r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + D s)‖ < 1 ∧
      (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = D s := fun s => by
    refine ((isClosed_small (c1.matrix_trace.sub (continuous_const.add hDc))).inter
      (isClosed_eq c1.matrix_det hDc)).closure_subset_iff.2 ?_ (hdense s)
    rintro σ ⟨w, hw, -, A, hA, hσ⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨⟨B₁, hB₁, hF⟩, hq⟩ := hw
    have hqN : ¬ normV w ∣ N := fun h => hq (h.mul_left _)
    obtain ⟨B₂, hB₂, e⟩ := hsat w ((hc0 w).2 hqN)
    obtain rfl := hB₁.unique hB₂
    obtain ⟨h2, h3⟩ := tr_det ι _ (((hF A hA).2 σ hσ).trans e)
    have hAq := (over_iff hA _).2 dvd_rfl
    have h1 : (D σ : Qbar l) = ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1)) := by
      rw [hDv, cyc_frob (normV_prime w) hAq (fun h => hq (h.mul_right _)) hσ, dirG_frob _ (normV_prime w) hAq hqN hσ]
      simp [mul_comm]
    have h4 := hg _ (normV_prime w)
    rw [map_sub, map_add (f := _), map_one, ← h1, ← h2] at h4
    exact ⟨h4, by rw [Set.mem_setOf_eq, h3, h1, (hval w hqN).2]⟩
  have hlev : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl ℚ, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hker : ψ⁻¹.ker = ψ.ker := by ext s; simp
  refine ⟨levL l c, π, r, ⟨hreg, ⟨χ', hpol⟩, hG.cont, hatt, MonoidHom.ext fun s => ?_, ?_, ?_, fun w A hA => ?_, fun w hw => ?_,
    fun w hw hwl => ?_, fun w hw => ?_⟩, fun s => (hall s).1⟩
  · have h1 := (hall s⁻¹).2
    rw [inv_inv] at h1
    refine (Units.ext h1 : Matrix.GeneralLinearGroup.det (r s) = D s⁻¹).trans ?_
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, ← mul_inv, map_inv]
    rfl
  · rw [hker, ← hm]
    exact dirG_open _
  · refine (fin_dvd hlN).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · exact ((mem_iff w l).1 h).mul_right _
    · rw [Set.mem_setOf_eq, hlev w h, Ne, hc0, not_not] at hw
      exact hw.mul_left _
  · rw [hker, ← hm]
    by_cases h : normV w ∣ N
    · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hN ((mem_iff_eq w hl.out).1 h' ▸ h)
      rw [hlev w h1, hc0]
      exact iff_of_false (ram hχ _ (normV_prime w) h ((over_iff hA _).2 dvd_rfl)) (by simp [h, h1])
    · refine iff_of_true (fun s hs => dirG_unr _ (fun h' => h ((over_iff hA _).1 h')) hs) ?_
      by_cases h1 : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
      · exact Or.inr h1
      · exact Or.inl ((hlev w h1).trans ((hc0 w).2 h))
  · have h1 : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h' => by rw [hlev1 w h'] at hw; exact one_ne_zero hw
    obtain ⟨v, h2, h3, -⟩ := hU w
    rw [show N.factorization (normV w) = 0 from (hlev w h1).symm.trans hw] at h3
    exact ⟨v, h2, h3⟩
  · rw [hlev w hwl] at hw ⊢
    refine ⟨_, hU w, norm_eq_one_of ?_⟩
    have h4 := hg _ (normV_prime w)
    rw [Ne, hc0, not_not] at hw
    rwa [χ.map_nonunit (fun h' => (Nat.Prime.coprime_iff_not_dvd (normV_prime w)).1 ((ZMod.isUnit_iff_coprime _ _).1 h') hw),
      zero_mul, add_zero, map_sub, map_one] at h4
  · have hq := (mem_iff_eq w hl.out).1 hw
    have hqN : ¬ normV w ∣ N := hq ▸ hN
    obtain ⟨B, hB, e⟩ := hsat w ((hc0 w).2 hqN)
    rw [(hval w hqN).2] at e
    have h2 : ‖ι.symm (χ (normV w : ZMod N))‖ = 1 := by
      refine norm_root (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
      rw [← ZMod.coe_unitOfCoprime _ ((Nat.Prime.coprime_iff_not_dvd (normV_prime w)).2 hqN), ← map_pow, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one, map_one]
    have h3 : ‖(normV w : Qbar l)‖ < 1 := by rw [hq]; exact norm_l
    have hs : ‖ι.symm (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))‖ < ‖(normV w : Qbar l)‖ := by
      rw [map_mul, norm_mul, h2, one_mul, map_pow, map_natCast, norm_pow]
      exact pow_lt_self_of_lt_one₀ (norm_pos_iff.2 (Nat.cast_ne_zero.2 (normV_prime w).ne_zero)) h3 (by omega)
    have ha : ‖ι.symm (g.a (normV w)) - 1‖ < 1 := by
      have := small_add (hg _ (normV_prime w)) (hs.trans h3)
      rw [← map_add (f := _)] at this
      rw [← map_one ι.symm, ← map_sub]
      convert this using 3
      ring
    obtain ⟨lam, h5, h6⟩ := stab w ι π hB e ha hs
    refine ⟨hlev1 w hw, ?_, ?_, norm_one, ⟨lam, h5, ?_⟩, fun τ _ => hinf _⟩
    · simp; omega
    · simp
    · simpa using h6
end Gal
end UpperTheory.V.Sd.EG
end
end

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.ofOne0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → Third → Across → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ), IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K Ω)) → IsAutomorphicOverImagQuad ι r := by
  intro hP hT hA K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r θ hθ hd hirr haut hc K' _ _ _ inst _ tow hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨K'', _, _, _, _, _, hK'', h1, h2⟩ := hT K K' Ω hK hK' l n r hirr hirr'
  have h3 := hA K K'' Ω hK hK'' l ι n hn r θ hc hθ hd h1 haut
  rw [inf_comm] at h2
  have h4 := hA K'' K' Ω hK'' hK' l ι n hn r θ hc hθ hd h2 h3
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP K' Ω l ι n _).2.1.1 h4
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Ws UpperTheory.V.Cu UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix

private theorem algPos_of_expo (ω : HChar ℚ) (h : ∀ v, ∃ n : ℤ, TR.expo ω v = n) : ∃ a, IsAlgPos ω a := by
  obtain ⟨n, hn⟩ := h default
  refine ⟨fun _ => n, fun k hk => ?_⟩
  letI : Unique (ℚ →+* ℂ) := ⟨⟨Rat.castHom ℂ⟩, fun _ => Subsingleton.elim _ _⟩
  have hk0 : (0 : ℝ) < ((k : ℚ) : ℝ) := hk (Rat.castHom ℝ)
  let diagR : ℚ →+* TR.Rinf ℚ := (TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ))
  have hv : ∀ v, diagR (k : ℚ) v = ((k : ℚ) : ℝ) := fun v =>
    eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp diagR) (k : ℚ)
  have e : Units.map diagR.toMonoidHom k = TR.expU fun _ => Real.log ((k : ℚ) : ℝ) :=
    Units.ext (funext fun v => (hv v).trans (Real.exp_log hk0).symm)
  have hdiag : infDiag k = TR.infId ℚ (Units.map diagR.toMonoidHom k) := by
    have h : ((infDiag k : Ideles ℚ) : AdeleRing (𝓞 ℚ) ℚ) = (algebraMap ℚ (InfiniteAdeleRing ℚ) k, 1) := by
      unfold infDiag
      rw [MonoidHom.finsetProd_apply, Fintype.prod_unique, MonoidHom.comp_apply]
      refine Prod.ext (funext fun w => ?_) rfl
      have hw : w = default := Subsingleton.elim _ _
      subst w
      exact ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self ℚ default (atInf default k)
    apply Units.ext
    rw [h]
    refine Prod.ext ?_ ?_
    · change _ = 1 - TR.infEq ℚ 1 + TR.infEq ℚ ((TR.infEq ℚ).symm (algebraMap ℚ (InfiniteAdeleRing ℚ) k))
      simp
    · change (1 : Af ℚ) = 1 - 0 + 0
      simp
  have e2 := TR.chiInf_expU_eq ω fun _ => Real.log ((k : ℚ) : ℝ)
  rw [← e, Fintype.sum_unique, hn, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hk0] at e2
  rw [HChar.inf, MonoidHom.comp_apply, hdiag, Fintype.prod_unique, eq_ratCast, ← Complex.ofReal_ratCast]
  exact e2
private theorem det_sat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = ((x * y : ℂˣ) : ℂ) * q := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C]
  simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_apply]
  rw [Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_mul_mul_comm, hq', Units.val_mul, mul_comm]
private theorem det_alg (P : _root_.UpperTheory.V.Af.HypothesesH') {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous ρ) (ha : IsAutR ι ρ) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp ρ) := by
  obtain ⟨π, hreg, hatt⟩ := ha
  obtain ⟨ω, hω, hint⟩ := _root_.central_character_of_regular_cusp P.toClassicalTheorems π hreg (hatt.2.mono fun w ⟨B, hB, _⟩ => ⟨B, hB⟩)
  obtain ⟨a, hal⟩ := algPos_of_expo ω hint
  obtain ⟨art, hart⟩ : ∃ art : Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι hal
  have hch : IsCharOf ι ω μ := ⟨hμ, art, a, hart, hal, hL⟩
  obtain ⟨hcc, χ, art', a', h'⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic P.toClassicalTheorems.litN.aut.art ℚ Ω l ι 1 (cycBar ℚ Ω l)
    ⟨1, 1, le_rfl, fun _ _ => rfl, by rw [zpow_one, mul_one]⟩
  have H := (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).2.1
  have h1 : Af.IsAlgChar ι (cycBar ℚ Ω l) := ⟨χ, hcc, art', a', h'⟩
  have h2 := (H μ _ ⟨ω, hch⟩ (H _ _ h1 h1).2).1
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    have hp : l.Prime := Fact.out
    have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
    exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have key : (fun s : _root_.Formalism.ConjugateSelfDual.G ℚ Ω => (ρ s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det) =
      fun s => (((μ * (cycBar ℚ Ω l)⁻¹) s⁻¹ : (Qbar l)ˣ) : Qbar l) := by
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (Filter.eventually_cofinite.1 ((hatt.2.and (UpperTheory.galois_character_frobenius_compatibility ℚ Ω l ι ω μ hch)).and hl))
      (Units.continuous_val.comp (hc.comp continuous_inv)).matrix_det
      (Units.continuous_val.comp ((hμ.mul hcc.inv).comp continuous_inv)) ?_
    intro v hv _ A hA σ hσ
    obtain ⟨⟨⟨B, hB, hF⟩, -, h3⟩, h4⟩ := not_not.1 hv
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have hcyc : ι (((cycBar ℚ Ω l)⁻¹ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV v : ℂ) := by
      have hval : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob h4 hA hσ, map_natCast, map_natCast]
      rw [MonoidHom.inv_apply, map_inv, inv_inv, hval, map_natCast]
    apply ι.injective
    rw [MonoidHom.mul_apply, Units.val_mul, map_mul, (h3 A hA).2 σ hσ, hcyc,
      ← hω v x y hB, ← det_sat _ _ _ _ e2]
    exact ι.toRingHom.map_det _
  have e : Matrix.GeneralLinearGroup.det.comp ρ = μ * (cycBar ℚ Ω l)⁻¹ := MonoidHom.ext fun s => Units.ext (by
    have := congrFun key s⁻¹
    simp only [inv_inv] at this
    exact this)
  rw [e]
  exact h2
private theorem conj_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem conj_off {Ω : Type} [Field Ω] [CharZero Ω] (K' : IntermediateField ℚ Ω) (hK : IsTotallyComplex K') {c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω}
    (hc : IsConjEl c) : c ∉ K'.fixingSubgroup := by
  intro h
  obtain ⟨j, hj⟩ := hc
  refine InfinitePlace.not_isReal_iff_isComplex.2 (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K' Ω))))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
  exact (hj x).symm.trans (congrArg j (h x))
private theorem pair_plane {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem kap_anti {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {K' : IntermediateField ℚ Ω} [NumberField K'] {g0 : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} {m : ℕ} {c₁ : Coef l} {κ : _root_.Formalism.ConjugateSelfDual.G K' Ω →* (Qbar l)ˣ}
    {τ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* Sd.S3.M2 c₁.O} {s} (hτ : TauDat ι K' g0 m c₁ τ s κ) {c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω} (hc : c ∉ K'.fixingSubgroup) {g g' : _root_.Formalism.ConjugateSelfDual.G K' Ω}
    (h : resQ K' g' = c * resQ K' g * c⁻¹) : (κ g : Qbar l) * κ g' = 1 := by
  have hf : ∀ x, τ x 0 0 ^ 2 - τ x 1 0 ^ 2 = 1 := fun x => by
    have h := congrFun (congrFun (hτ.form x) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have hg : resQ K' g ∈ K'.fixingSubgroup := fun y => g.commutes y
  have e : τ (resQ K' g') * τ c = τ c * τ (resQ K' g) := by
    rw [h, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have hg' : resQ K' g' ∈ K'.fixingSubgroup := fun y => g'.commutes y
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 0) 1
  have f1 := hf c
  have f2 := hf (resQ K' g)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, (hτ.off c hc).1, (hτ.off c hc).2, (hτ.on _ hg).1, (hτ.on _ hg).2] at e0 e1 f1 f2
  have key : (τ (resQ K' g) 0 0 + τ (resQ K' g) 0 1) * (τ (resQ K' g') 0 0 + τ (resQ K' g') 0 1) = 1 := by
    generalize τ (resQ K' g) 0 0 = a at *
    generalize τ (resQ K' g) 0 1 = b at *
    generalize τ (resQ K' g') 0 0 = a' at *
    generalize τ (resQ K' g') 0 1 = b' at *
    generalize τ c 0 0 = p at *
    generalize τ c 0 1 = q at *
    linear_combination (a + b) * (p + q) * (e0 - e1) + f2 - (a + b) * (a' + b' - a + b) * f1
  rw [hτ.val g, hτ.val g']
  exact_mod_cast congrArg (fun z : c₁.O => (z : Qbar l)) key
theorem UpperTheory.V.Cu.polOf4_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Cu.PolOf4 := by
  intro P Ω _ _ _ l _ ι K' _ _ hK ρ hρ ha g0 m c₁ κ τ s hτ
  obtain ⟨c, hc⟩ := conj_ex Ω
  let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J * ρ c⁻¹, det_alg P ι ρ hρ ha,
    fun a b h h' => auSign _ a b h h', hc, fun g g' h => ?_⟩
  have h' : resQ K' g' = c * resQ K' g * c⁻¹ := h
  have hk := kap_anti hτ (conj_off K' hK hc) h'
  have e : ρ c⁻¹ * ρ (resQ K' g') = ρ (resQ K' g) * ρ c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (ρ c⁻¹).val * (ρ (resQ K' g')).val = (ρ (resQ K' g)).val * (ρ c⁻¹).val := congrArg Units.val e
  have hp : (ρ (resQ K' g)).valᵀ * J.val * (ρ (resQ K' g)).val = (ρ (resQ K' g)).val.det • J.val := pair_plane _
  have hd : (((Matrix.GeneralLinearGroup.det.comp ρ).comp (resG ℚ K' Ω) g : (Qbar l)ˣ) : Qbar l) = (ρ (resQ K' g)).val.det := rfl
  rw [hd, tw_val, tw_val, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.val_mul, ← Matrix.smul_mul, ← hp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk, one_smul]
  simp only [Matrix.mul_assoc, e']
end
end
end
