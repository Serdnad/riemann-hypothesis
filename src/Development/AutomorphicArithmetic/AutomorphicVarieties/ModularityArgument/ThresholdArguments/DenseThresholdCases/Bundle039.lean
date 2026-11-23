module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle085
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle064
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle061
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle029
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle009
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle011
import GroundTheory.LocalFields.UnramifiedHensel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem isoOfFrobOne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : _root_.Formalism.ConjugateSelfDual.G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : _root_.Formalism.ConjugateSelfDual.G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : _root_.Formalism.ConjugateSelfDual.G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
private theorem normV_one {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) (h : w.asIdeal.inertiaDeg ℤ = 1) : normV w = normV (w.under (𝓞 K)) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg_tower (R := ℤ) (w.under (𝓞 K)).asIdeal w.asIdeal] at h
  rw [normV_under (K := K) w, Nat.eq_one_of_mul_eq_one_left h, pow_one]
theorem UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det :
    ∀ (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : DescS) (hG : GapTwo) (hR : ExRTwo) (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
      [Algebra M Ω] [IsScalarTower ℚ M Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure M Ω] (hp : Module.finrank ℚ M = 2) (hM : IsCMField M)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (hr : Continuous r)
      (hirr : IsIrr (r.comp (resG ℚ M Ω))) (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1), IsAut ι (r.comp (resG ℚ M Ω)) → IsAut ι r := by
  intro H cyc hG hR M Ω _ _ _ _ _ _ _ _ hp hM l _ ι r hr hirr hfin
  haveI : Algebra.IsQuadraticExtension ℚ M := ⟨hp⟩
  have hK : IsTotallyReal ℚ := inferInstance
  have hdown := cyc M hp inferInstance
  have hss : IsSSRep (r.comp (resG ℚ M Ω)) := (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ 2 r).1 _ hirr
  have hcont := continuous_restrictScalarsHom ℚ M Ω
  rintro ⟨sat', inf', hc', hreg', hatt'⟩
  have hgap : Gap2 inf' := by
    rcases hc' with ⟨_, P, rfl, rfl⟩ | ⟨hR', -⟩
    · refine hG M Ω l ι _ P ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hatt' (hfin.imp fun N h => ⟨h.1, fun s => h.2 _⟩)
      obtain ⟨m, hm, h⟩ := hreg' τ
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) hm]
      exact h
    · exact (not_both M hR' inferInstance).elim
  obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' hgap (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ M Ω l ι 2 r sat' hatt')
  have hreg : RegInf 2 inf := fun τ => by
    obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
    have := hinf _ m hm
    rw [ComplexEmbedding.lift_comp_algebraMap] at this
    exact ⟨m, this, h⟩
  obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
    rcases hc with ⟨hC, -⟩ | ⟨hR', π, rfl, rfl⟩
    · exact (not_both ℚ hK hC).elim
    · obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt H.toClassicalTheorems ℚ π
      refine hR ℚ Ω l ι π ω (fun v => ?_) ⟨fun v v' => by rw [Subsingleton.elim v v'], _root_.UpperTheory.V.Sd.Wc.polGL2_alt H.toClassicalTheorems ℚ π ω hω⟩
      have := hreg v.embedding
      simpa only [InfinitePlace.mk_embedding] using this)
  have hN := (UpperTheory.galois_representation_image_spec ℚ M Ω).1
  have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ 2 r₁ (resG ℚ M Ω) hN hatt₁.1
  have hiso : RepIso (r₁.comp (resG ℚ M Ω)) (r.comp (resG ℚ M Ω)) := by
    refine isoOfFrobOne M Ω l ι 2 _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
    filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under ℚ M).eventually hatt₁.2, hatt'.2]
      with w h1 ⟨B₁, hB₁, h₁⟩ ⟨B', hB', h'⟩ hd
    have hn := normV_one (K := ℚ) w hd
    obtain ⟨B, hB, hP⟩ := h1 hn
    obtain rfl := cusp_unique hc _ _ _ hB hB₁
    obtain rfl := cusp_unique hc' _ _ _ hP hB'
    have h3 := (UpperTheory.frobenius_power_compatibility ℚ M Ω l ι w 1 (by rw [pow_one]; exact hn)).1 2 r₁ _ h₁
    simp only [pow_one, Multiset.map_id'] at h3
    rw [← hn] at h3
    exact ⟨_, h3, h'⟩
  obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ 2 r r₁ (resG ℚ M Ω) hN hirr hiso
  have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
  obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H ℚ Ω l ι 2 r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
    (hF.1 ℚ Ω l ι δ (hF.2 ℚ M Ω l δ hδ))
  exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr',
    hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
end
end

section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing



section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
theorem UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound :
    _root_.UpperTheory.V.Af.NumberSp4Alt → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
  classical
  rintro ⟨C, A, hnum⟩
  refine ⟨C, A, ?_⟩
  intro Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut
  have hlp : l ≠ p := fun h => hpS (h ▸ hD.l_mem)
  obtain ⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  have hB : ML.Over (D.pl p) p := hD.pl_over p hp
  obtain ⟨σ, hσ⟩ := hfr _ p hp hB
  obtain ⟨w, hw, -, hpw⟩ := hpl _ p hp hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have hχ : (((chiO ℚ Ω l c.O σ : c.Oˣ) : c.O) : PadicAlgCl l) = (p : PadicAlgCl l) := by
    have hz : (cycZ ℚ Ω l σ : ℤ_[l]) = (p : ℤ_[l]) := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      exact cycZ_toZModPow_eq hlw hw hσ.2 n
    simp only [chiO, MonoidHom.comp_apply, Units.coe_map]
    rw [hz]
    simp
  have h3 : (D.om⁻¹ * D.ξ) ^ k = 1 := by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]
  have h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1 := by rw [mul_pow, h3, hψ, one_mul]
  have mapped_pow (χ : G ℚ Ω →* c.Oˣ) (h : χ ^ k = 1) :
      ι ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
    have hσpow : χ σ ^ k = 1 := by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [← map_pow]
    have hcast : ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
      rw [← Subalgebra.coe_pow, ← Units.val_pow_eq_pow_val, hσpow]
      rfl
    rw [hcast, map_one]
  obtain ⟨NN, hNN, hlog, hX⟩ := hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _
    (mapped_pow _ h1) (mapped_pow _ hψ) (mapped_pow _ h3)
  replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ
  have htrace : (D.r0E σ).trace = ι.symm (Af.eis4 p D.e
      (ι (((D.om⁻¹ * D.ξ * D.ψ) σ : c.O) : PadicAlgCl l))
      (ι ((D.ψ σ : c.O) : PadicAlgCl l)) (ι (((D.om⁻¹ * D.ξ) σ : c.O) : PadicAlgCl l))) := by
    have hsum : (D.r0E σ).trace = ∑ i, (((D.ps i σ : c.Oˣ) : c.O) : PadicAlgCl l) := by
      simp [Raw.r0E, Raw.r0, mapRep, diagRep, Matrix.trace]
    rw [hsum]
    simp only [Fin.sum_univ_four, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, Af.eis4, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      zpow_natCast, MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Subalgebra.coe_mul, Subalgebra.coe_one,
      Subalgebra.coe_pow, map_add, map_mul, map_pow, map_natCast, map_one, RingEquiv.symm_apply_apply, hχ]
    ring
  rw [← htrace] at hX
  have hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩
  have hne : D.AllIrr (fun r => D.aVal σ r ≠ 0) := by
    intro r hr hi
    have h := (hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi)
      (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _
      (Finset.mem_singleton_self _)
    exact sub_ne_zero.2 h
  refine ⟨σ, hne, ?_⟩
  rintro ⟨-, Xi, hXi, hconj, hle⟩
  have hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits := fun r r' h =>
    MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)
  have h := (hX (Xi.image fun r => r.toHomUnits) (fun s hs => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hs'
      rw [hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2
  rw [Finset.prod_image hinj.injOn] at h
  change _ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hNN)
  have h4 := Real.log_le_log hN0 h
  rw [Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)] at h4
  have h5 : -Real.log ‖(NN : PadicAlgCl l)‖ ≤ Real.log |(NN : ℝ)| := by
    have hq : (NN : ℚ) ≠ 0 := by exact_mod_cast hNN
    have hx : ‖(NN : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℤ)) := by
      have hc : (((NN : ℚ) : ℚ_[l]) : PadicAlgCl l) = (NN : PadicAlgCl l) := by simp
      rw [← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
      have hnorm := padicNorm.eq_zpow_of_ne_zero (p := l) hq
      rw [padicValRat.of_int] at hnorm
      rw [hnorm]
      push_cast
      rfl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    have hdvd : ((l : ℤ) ^ padicValInt l NN) ∣ NN := padicValInt_dvd NN
    have hle : ((l : ℤ) ^ padicValInt l NN) ≤ |NN| :=
      Int.le_of_dvd (abs_pos.mpr hNN) ((dvd_abs _ _).mpr hdvd)
    have hle' : (l : ℝ) ^ padicValInt l NN ≤ |(NN : ℝ)| := by exact_mod_cast hle
    rw [hx, Real.log_zpow]
    push_cast
    rw [neg_mul, neg_neg, ← Real.log_pow]
    exact Real.log_le_log (pow_pos hl0 _) hle'
  have h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤
      C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p := by
    have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have := Real.log_natCast_nonneg p
    gcongr
  rw [Finset.sum_neg_distrib] at hle
  linarith
end
end

section




section
noncomputable section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
namespace UpperTheory.V.Z.J
section Pt
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
end Pt
section Heads
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base
open UpperTheory.V.Alg UpperTheory.V.Th
end Heads
section Count
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Published
structure Adm3U_s {l : ℕ} [Fact l.Prime] {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop extends toAdm3 : _root_.UpperTheory.V.Af.Adm3Alt ι e N ρ where
  unl : Th.Unl l N ![(e : ℤ), 0, -(e : ℤ)] ρ
def NumberU3U_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∃ c A : ℕ,
    ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → 7 ≤ p →
      ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K →
    ∀ (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) →
      (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Fintype.card Orb * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w →
        ∀ σ : G K Ω, IsFrob B (normV w) σ →
        ∀ X : Orb → Finset (G K Ω →* GL (Fin 3) (Qbar l)),
          (∀ o, ∀ ρ ∈ X o, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) →
          (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') →
          (∀ o, ∀ ρ ∈ X o, (ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 (normV w) e (z o))) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤
            ∏ o, ∏ ρ ∈ X o, ‖(ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 (normV w) e (z o))‖
end Count
section One
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Base
def OneCharU_s : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N),
    GD Ω K l e ψ → ∀ (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l),
    t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)) →
    (∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) →
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t)
def AdmI_s : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
    {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f →
    ∀ (hr : HasMult D.η (push f S.r.hom)) (ι : Qbar l ≃+* ℂ), U3.TypeI D.η (push f S.r.hom) → D.IsAutIAlt ι (push f S.r.hom) hr →
      _root_.UpperTheory.V.Z.J.Adm3U_s ι e N (D.rhoK (push f S.r.hom) hr)
end One
end UpperTheory.V.Z.J
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.V0
private theorem ePart_zero {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ 0 0 = ⊤ := by
  simp [ePart, opE]
private theorem card_not_dvd {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (j : ℕ) : ¬ l ∣ Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j := by
  have hl : l.Prime := Fact.out
  have hw : (s.w s.v0).under (𝓞 (Lp L)) = s.v0 := by
    ext x
    exact (s.hw s.v0 (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA s.v0 x)
  have h2 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← s.norm_v0_eq_one, normV, ← nsmul_one]
    exact card_nsmul_eq_zero'
  have h3 : ((s.p : ℕ) : 𝓞 L) ∈ (s.w s.v0).asIdeal := by
    rw [← hw] at h2
    have h4 : algebraMap (𝓞 (Lp L)) (𝓞 L) ((s.p : ℕ) : 𝓞 (Lp L)) ∈ (s.w s.v0).asIdeal := h2
    rwa [map_natCast] at h4
  have hd : Ideal.absNorm (s.w s.v0).asIdeal ∣ Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h3)
  have hn : Ideal.absNorm (Ideal.span {((s.p : ℕ) : 𝓞 L)}) = s.p ^ Module.finrank ℤ (𝓞 L) := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 L)), Algebra.norm_algebraMap]
    simp [Int.natAbs_pow]
  rw [hn] at hd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow s.p_prime).1 hd
  have hq : Nat.card 𝓀[(s.w s.v0).adicCompletion L] = s.p ^ e :=
    (resCard_eq_normV _).trans (by rw [normV, ← Ideal.absNorm_eq_natCard, he])
  intro h
  rw [hq] at h
  exact s.p_ne ((Nat.prime_dvd_prime_iff_eq hl s.p_prime).1 (hl.dvd_of_dvd_pow (hl.dvd_of_dvd_pow h))).symm

theorem z_eq_dim_e_of_count_e_res_eq_inv_loc_kir : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo → InvEq1 → InvBox → LocE → KirCusp → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt := by
  intro hCount hRes hInv hBox hLoc hKir hP hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV hn4
  obtain ⟨a, j, D₀, hE, hD₀, hdim⟩ := hLoc ((s.w s.v0).adicCompletion L) n
  refine ⟨a, Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j, hE, card_not_dvd s j, ?_⟩
  intro Q c r ι m τ₀ hτ A _ _ _ θ hθ lam K D D' h h'
  obtain ⟨a₀, ha⟩ := hCount hP hM hC l L Ω s n hn V hV hn4 ι lam
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : IsAdicComplete (maximalIdeal c.O) c.O := hc
    have : Finite (ResidueField c.O) := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rwa [← map_natCast (residue c.O), residue_eq_zero_iff]
    have : CharP (c.O ⧸ maximalIdeal c.O) l :=
      inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hτ (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  obtain ⟨χ, hχ, hext⟩ : ∃ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ ∧
      ∀ (u : s.St) (i : Fin n), ∃ ψ : Weil (s.hw u) →* ℂˣ, ∀ g, ψ (ineIncl (s.hw u) g) = χ u i g :=
    ⟨_, hτ t ht, fun u i => ⟨W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
      ((t i).comp (V.pr.comp (Weil (s.hw u)).subtype)), fun _ => rfl⟩⟩
  have key : ∀ D : ℕ, _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) D →
      ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
        (∀ (u : s.St) rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (C.u u)))) ∧
        (D : Cardinal) = a₀ * (Module.rank ℂ (cInv1 C ι τ₀) * D₀) ∧ 1 ≤ D := by
    rintro _ ⟨x, d, ξ, c0, sp, ev, hs, hu, hz, hall, rfl⟩
    obtain ⟨e, he⟩ := hs.alg
    obtain ⟨π, σ, C, h1, h2, h3, h4, h5⟩ := ha Q c r m τ₀ hτ d e ξ he A θ x c0 sp hθ hs K ev hu hz hall
    haveI : FiniteDimensional ℂ (zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) :=
      haveI := hs.fin K c0 le_rfl
      Submodule.finiteDimensional_of_le (S₂ := (hset Q τ₀).ClAt θ ι x.toRingHom lam ξ K c0)
        (inf_le_left.trans (iSup_le fun _ => inf_le_left))
    have hb := fun (a' : GLw n (s.w s.v0) →₀ ℤ) (N' : ℕ) => hBox _ _ _ _ (piRep fun u => (C.u u).ρ) C.o.ρ m (KT n (wt s)) (Kc _ n 1)
      ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) a' N'
    have h0 := h5 0 0 (by simp)
    have hz0 : Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev) ≠ 0 :=
      fun hf => hz (Submodule.finrank_eq_zero.1 hf)
    rw [show eC Q τ₀ d 0 0 = ⊤ from ePart_zero _, inf_top_eq, hb 0 0, ePart_zero, inf_top_eq] at h0
    have hne : (a₀ : Cardinal) * (Module.rank ℂ (cInv1 C ι τ₀) * Module.rank ℂ ↥(fixd C.o.ρ (Kc _ n 1))) ≠ 0 :=
      h0 ▸ Nat.cast_ne_zero.2 hz0
    have ha₀ : (a₀ : Cardinal) ≠ 0 := left_ne_zero_of_mul hne
    have hr : Module.rank ℂ (cInv1 C ι τ₀) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hf : fixd C.o.ρ (Kc _ n 1) ≠ ⊥ := fun hf => right_ne_zero_of_mul (right_ne_zero_of_mul hne) (by rw [hf]; simp)
    have hd := hdim _ C.o.ρ C.o.smooth (hKir L n hn π (s.w s.v0) C.o h2) hf
    have hD := h5 a (Nat.card 𝓀[(s.w s.v0).adicCompletion L] ^ j) hE.supp
    rw [hb, hd] at hD
    refine ⟨π, σ, C, h1, fun u rc hrc =>
      _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ h4 h3 χ hχ C.u C.hu u rc hrc, hD, ?_⟩
    refine Nat.one_le_iff_ne_zero.2 fun h0' => ?_
    rw [h0', Nat.cast_zero] at hD
    exact mul_ne_zero ha₀ (mul_ne_zero hr (Nat.cast_ne_zero.2 hD₀.ne')) hD.symm
  obtain ⟨π, σ, C, a1, a3, a5, a6⟩ := key D h
  obtain ⟨π', σ', C', b1, b3, b5, -⟩ := key D' h'
  have hr : Module.rank ℂ (cInv1 C ι τ₀) = Module.rank ℂ (cInv1 C' ι τ₀) :=
    hInv l L Ω s n hn V hV c ι m τ₀ σ σ' C C'
      (fun u => hRes hP.litN L Ω n hn π π' (s.w u) (s.A u) (s.hw u) (C.u u) (C'.u u) (a1 u) (b1 u) (χ u) (hext u) (a3 u) (b3 u))
  rw [hr, ← b5] at a5
  exact ⟨a6, Nat.cast_injective (R := Cardinal) a5⟩
end UpperTheory.V.Z.Desc.V0
end
end
end
