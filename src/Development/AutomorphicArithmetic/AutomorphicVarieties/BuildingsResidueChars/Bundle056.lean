module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle044
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle049
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle035
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
import Mathlib.RingTheory.Ideal.Norm.RelNorm
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.polOfSat_of_thetaSat :
    UpperTheory.V.Af.Bc.ThetaSat → UpperTheory.V.Af.Bc.PolOfSat := by
  intro hθ hJ hG E _ _ _ n hn P ψ h
  refine GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E n P ψ (hG E n _) ?_
  have hiso : (GlobalTheory.ThetaPull.thetaSub P).Iso (P.twist ψ⁻¹) := by
    refine Quotient.exact (hJ.strong_multiplicity_one hn (CG.mk (GlobalTheory.ThetaPull.thetaSub P)) (CG.mk (P.twist ψ⁻¹)) ?_)
    refine h.mono fun w ⟨hu, B, B', h1, h2, e⟩ => ⟨B'.map (·⁻¹), hθ E n P w B' h2, ?_⟩
    have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
      have h3 : ψ.loc w x = 1 := hu x hx
      exact (congrArg Inv.inv h3).trans inv_one
    rw [e]
    exact GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' h1
  obtain ⟨T, hT⟩ := hiso
  refine ⟨((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm)).trans
    (hT o ((GlobalTheory.ThetaPull.pull E n).submoduleMap P.V φ))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

private theorem exists_sign {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) : ∃ m : ℕ, ∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩
  · exact ⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩

theorem UpperTheory.heckeChar_sign_fixed :
    UpperTheory.V.Af.Bc.SignFix := by
  intro E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n
  obtain ⟨m, hm⟩ := exists_sign (surjective_algebraMap_real E hE) χ
  have ho : (quadChar E ^ (m + n)).OrderDvd 2 := by
    have := quadChar_order E
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hη := isAlgPos_zero_of_orderDvd two_pos ho
  obtain ⟨δ, hδc, hδ⟩ := ha.exists_isLAdicOf ι hη
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  have h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹ := by
    rw [map_one, one_mul, eq_comm, inv_eq_one]
    exact Subtype.ext (MonoidHom.ext fun x => inv_one)
  have hres := GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)
  refine ⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  · rw [MonoidHom.mul_comp, hres, zpow_zero, mul_one]
  · change χ.locInf v (-1) * (quadChar E ^ (m + n)).locInf v (-1) = (-1) ^ n
    rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

private theorem sat_of_isoTwist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} {π : TR.CuspSub F n}
    {η : HChar F} (h : IsoTwist π η) {v : HeightOneSpectrum (𝓞 F)} (hη : η.UnrAt v) {B : Multiset ℂˣ}
    (hB : π.HasSat v B) : B = B.map (· * η.val v) := by
  obtain ⟨T, hT, -⟩ := h
  refine hB.unique (GlobalTheory.SphGal.hasSatGL_of_twist hη T.symm (fun g x => ?_) hB)
  obtain ⟨x, rfl⟩ := T.surjective x
  apply T.injective
  rw [LinearEquiv.symm_apply_apply, TR.CuspSub.locRep_eq, hT, map_smul, LinearEquiv.apply_symm_apply,
    TR.CuspSub.chiDet_locGL]
  rfl

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

theorem UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible :
    UpperTheory.V.Af.IsoOfFrob → UpperTheory.V.Af.Bc.FrobTw → UpperTheory.V.Af.Bc.SignEx → UpperTheory.V.Af.Bc.SignFrob → UpperTheory.V.Af.Bc.SchurTw → UpperTheory.V.Af.Bc.IrrBasic → UpperTheory.V.Af.Bc.NoTwist := by
  intro hIso hTw hEx hFr hSch hIrr F E Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι h2 n r π hc hatt hirr η hη hT
  obtain ⟨δ, hδc, hδ1, hδs, hδu⟩ := hEx F E Ω l h2
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    exact Algebra.IsAlgebraic.trans F E Ω⟩
  refine hδ1 (hSch _ _ _ n r (res F Ω E) δ hirr ?_ ?_)
  · ext s
    have := (hδs.1 _).2 ⟨s, rfl⟩
    simpa using this
  · refine hIso F Ω l ι n r _ hc (hIrr.2 _ _ n r δ hc hδc) hatt.1 ((hIrr.1 _ (_root_.Formalism.ConjugateSelfDual.G F Ω) _ n r).2.2 δ hatt.1) ?_
    filter_upwards [hatt.2, hδu, eventually_under (F := F) hη] with v hv hu hw
    obtain ⟨w, rfl, hw⟩ := hw
    obtain ⟨B, hB, hE⟩ := hv
    obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
    refine ⟨_, hE, ?_⟩
    have h4 := hTw F Ω l ι n r δ _ _ _ hE (hFr F E Ω l ι δ hδs w hu)
    convert h4 using 1
    conv_lhs => rw [sat_of_isoTwist hT h1 hB]
    have h5 : ((η.val (w.under (𝓞 F)) : ℂˣ) : ℂ) = if normV w = normV (w.under (𝓞 F)) then 1 else -1 := by
      refine (congrArg Units.val h3).trans ?_
      change ((if normV w = normV (w.under (𝓞 F)) then 1 else -1 : ℂˣ) : ℂ) = _
      split_ifs <;> simp
    simp only [algSat_eq, Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [← h5]
    simp only [Function.comp_apply, Units.val_mul, mul_assoc]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq w, norm_eq (w.under (𝓞 K))]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
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

theorem UpperTheory.baseChange_attached_of_frobenius_restriction :
    UpperTheory.V.Af.Bc.FrobRes → UpperTheory.V.Af.Bc.BcAtt := by
  intro hres F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π P hbc
  refine ⟨fun hreg => (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, fun hatt hss => ⟨hss, ?_⟩⟩
  · obtain ⟨m, hm, hnd, hz⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hbc.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · filter_upwards [hbc.unr, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
    obtain ⟨B, hB, hP⟩ := h1 (w.under (𝓞 F)) rfl _ (normV_under (K := F) w)
    obtain ⟨B', hB', hF⟩ := h2
    obtain rfl := TR.CuspSub.HasSat.unique hB hB'
    refine ⟨_, hP, ?_⟩
    have h3 := (hres F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
    rw [← algSat_pow, ← normV_under] at h3
    exact h3
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem key {Q V B B' : Type} [Field Q] [AddCommGroup V] [Module Q V] [CommRing B] [Algebra Q B]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (T : V →ₗ[Q] V) (c : B →ₗ[Q] B')
    (w w' : Fin n → B) (h : ∀ i, ∑ j, algebraMap Q B (e.repr (T (e j)) i) * w' j = w i) :
    ∑ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (w i) := by
  have h1 : ∀ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (algebraMap Q B (e.repr (T (e j)) i) * w' j) := by
    intro j
    conv_lhs => rw [← e.sum_repr (T (e j))]
    rw [sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul, ← Algebra.smul_def, map_smul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [← tmul_sum, ← map_sum, h]

private theorem eq_zero {Q V B' : Type} [Field Q] [AddCommGroup V] [Module Q V]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (w : Fin n → B')
    (h : ∑ i, e i ⊗ₜ[Q] w i = 0) (k : Fin n) : w k = 0 := by
  have := congrArg (fun x => TensorProduct.lid Q B' (LinearMap.rTensor B' (e.coord k) x)) h

  simpa [map_sum, Finsupp.single_apply, ite_smul] using this

private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (k : ℕ) (v : LL) (b : P.R.B) :
    (phiV P LL LL ^ k) (v ⊗ₜ C b) = v ⊗ₜ C ((P.φB ^ k) b) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, AlgHom.mul_apply]

theorem UpperTheory.weilDeligne_unramified_period :
    UpperTheory.V.Af.Wd.UnrPer := by
  intro l _ K L η hη hI
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  have hη' : Continuous fun g => (η g : ↥L.1) := continuous_induced_rng.2 hη
  obtain ⟨n, e, M, hMc, hM⟩ := UpperTheory.galois_representation_integral_lattice l ↥(GK K) ↥L.1 (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η))
    (fun x => hη'.mul continuous_const)
  obtain ⟨W, hW, hWg, hWφ⟩ := UpperTheory.crystalline_frobenius_algebraic_elements l K n M hMc (fun g hg => by
    rw [← map_one M]
    ext i j
    rw [hM, hM, map_one]
    congr 2
    change (η g : ↥L.1) * e j = e j
    rw [hI g hg, Units.val_one, one_mul])
  haveI := nontrivial_B (V.Loc.PP l)
  haveI : Nonempty (Fin n) := e.index_nonempty
  let j₀ : Fin n := Classical.arbitrary _
  let c : V.Loc.Bcr l →ₗ[ℚ_[l]] Bst (V.Loc.PP l) := (CAlgHom : V.Loc.Bcr l →ₐ[ℚ_[l]] Bst (V.Loc.PP l)).toLinearMap
  have hk : ∀ (g : ↥(GK K)) (f : V.Loc.Bcr l → V.Loc.Bcr l),
      (M g).map (fun z => algebraMap ℚ_[l] (V.Loc.Bcr l) (z : ℚ_[l])) * W.map f = W →
      ∑ j, ((η g : ↥L.1) * e j) ⊗ₜ[ℚ_[l]] (C (f (W j j₀)) : Bst (V.Loc.PP l)) = ∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀) := by
    intro g f h
    refine key e (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η) g) c (fun i => W i j₀) (fun i => f (W i j₀)) fun i => ?_
    have := congrFun (congrFun h i) j₀
    simpa only [Matrix.mul_apply, Matrix.map_apply, hM] using this
  refine ⟨∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀), fun h0 => ?_, fun g => ?_, fun g k hg => ?_⟩
  · refine hW.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_)
    exact C_eq_zero.1 (eq_zero e (fun i => (C (W i j₀) : Bst (V.Loc.PP l))) h0 i)

  · rw [map_sum]
    simp only [stRep_tmul, actSt_C]
    exact hk g _ (hWg g)

  · rw [map_sum, Finset.smul_sum]
    simp only [phiV_pow, smul_tmul']
    exact hk g _ (hWφ g k hg)
end

section

open Module

private theorem finrank_add_of_exact {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A] [FiniteDimensional k B] (f : A →ₗ[k] B)
    (p : B →ₗ[k] C) (hp : Function.Surjective p) (hex : Function.Exact f p) :
    finrank k (LinearMap.ker f) + finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.exact_iff.mp hex] at h2
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weil_deligne_functor_exactness :
    UpperTheory.V.Af.Wd.WdExact := by
  intro l _ ι K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hV', hV'', hds⟩ := UpperTheory.dpst_right_exact l K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨-, hde⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  haveI : FiniteDimensional ↥L.1 V' := FiniteDimensional.of_injective f hfi
  haveI : FiniteDimensional ↥L.1 V'' := Module.Finite.of_surjective p hps
  have key : Function.Exact (wdLin (UpperTheory.V.Loc.PP l) ι hf) (wdLin (UpperTheory.V.Loc.PP l) ι hp) ∧
      Function.Surjective (wdLin (UpperTheory.V.Loc.PP l) ι hp) :=
    letI := algC ι L
    UpperTheory.weilDeligne_functor_exact _ _ _ _ _ ℂ (mulD (UpperTheory.V.Loc.PP l) ρ') (mulD (UpperTheory.V.Loc.PP l) ρ) (mulD (UpperTheory.V.Loc.PP l) ρ'') (urC ι)
      (dmap (UpperTheory.V.Loc.PP l) hf) (dmap (UpperTheory.V.Loc.PP l) hp) _ _ hde hds
  refine ⟨hV', hV'', ?_, key.2, key.1⟩
  haveI := hV.finite
  haveI := hV'.finite
  have h1 := finrank_add_of_exact _ _ key.2 key.1
  have h2 := finrank_add_of_exact f p hps hex
  rw [LetterDim.finrank_wdSpace l _ ι K L V ρ hV, LetterDim.finrank_wdSpace l _ ι K L V' ρ' hV',
    LetterDim.finrank_wdSpace l _ ι K L V'' ρ'' hV''] at h1
  rw [LinearMap.ker_eq_bot.mpr hfi, finrank_bot] at h2
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  classical
  have := D.fin
  letI : Fintype D.S := Fintype.ofFinite D.S
  let f : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have key : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (f o s) ∧
      Real.log ‖f o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact UpperTheory.eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf0 : ∀ o s, f o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (key o s).1)
  obtain ⟨n, hn⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun p => f p.1 p.2) (fun p => (key p.1 p.2).2.1) (by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    obtain ⟨v, hv⟩ := D.conj σ
    refine ⟨u.prodCongr v, fun p => ?_⟩
    simp [f, eis3, hu, hv])
  refine ⟨n, ?_, ?_, ?_⟩
  · intro h
    rw [h, Int.cast_zero] at hn
    exact Finset.prod_ne_zero_iff.2 (fun p _ => hf0 p.1 p.2) hn.symm
  · have h1 : |(n : ℝ)| = ∏ p : Orb × D.S, ‖f p.1 p.2‖ := by
      rw [← norm_prod, ← hn, Complex.norm_intCast]
    rw [h1, Real.log_prod (fun p _ => norm_ne_zero_iff.2 (hf0 p.1 p.2))]
    refine (Finset.sum_le_sum (fun p _ => (key p.1 p.2).2.2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, nsmul_eq_mul]
    push_cast
    exact le_rfl
  · intro l _ hl ι Γ _ g admitted hcl X hX hinj
    obtain ⟨cl, hc1, hc2⟩ := hcl
    refine ⟨fun o ρ hρ h => ?_, ?_⟩
    · rw [hc2 ⟨ρ, hX o ρ hρ⟩] at h
      exact (key o _).1 (ι.symm.injective h)
    · have hq1 : ‖(q : Qbar l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
      have h2 := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S _ f (fun o s => (key o s).2.1) X
        (fun o r => cl ⟨r.1, hX o r.1 r.2⟩)
        (fun o r r' h => Subtype.ext (hinj o _ r.2 _ r'.2 (hc1 _ _ h)))
      rw [← Fintype.prod_prod_type', ← hn, map_intCast] at h2
      refine h2.trans (le_of_eq (Finset.prod_congr rfl fun o _ => ?_))
      rw [← Finset.prod_coe_sort (X o)]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hc2 ⟨r.1, hX o r.1 r.2⟩]
      simp only [f, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, hq1, one_pow, one_mul]
end
