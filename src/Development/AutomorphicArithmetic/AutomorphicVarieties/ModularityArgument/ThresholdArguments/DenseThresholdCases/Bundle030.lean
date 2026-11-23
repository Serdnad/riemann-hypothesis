module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle203
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle007
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle041
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LevelAt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Z.Bc
section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
private theorem lie_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    ∑ i, lieS E a i i z ψ = dchi ω z • ψ := by
  have e2 : lie E a (Central.scL a z) = ∑ i, lieS E a i i z := by

    simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => z)).symm
  rw [← LinearMap.sum_apply, ← e2]
  refine Subtype.ext (funext fun g => ?_)
  have h1 := Central.hasDerivAt_scalar z ψ g
  have h2 : (fun t : ℝ => ψ.1 (g * Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    have h3 := congrFun (congrArg Subtype.val (hω (infId E (expU (t • z))) ψ hψ)) g
    have h4 := chiInf_expU ω (t • z)
    rw [map_smul, Complex.real_smul] at h4
    rw [← h4]
    exact h3
  rw [h2] at h1
  have h5 := (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)
  have h6 := h1.unique h5
  change lieD _ ψ.1 g = dchi ω z * ψ.1 g
  rw [h6]
  simp
private theorem expo_central {π : CuspSub E a} {ω : HChar E} (hω : π.HasCentral ω) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : expo ω τ = m.sum := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine smul_left_injective ℂ h0 ?_
  beta_reduce
  rw [← GlobalTheory.trace_Eop_of_hasInfChar E a π τ m hm φ hφ]
  have h1 := lie_central hω (atEmb τ 1) hφ
  have h2 := lie_central hω (atEmb τ Complex.I) hφ
  simp only [Eop, expo, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, ← Finset.smul_sum, Finset.sum_sub_distrib, h1, h2]
  module
private theorem det_algSat (M : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (x y : ℂˣ)
    (h : M.charpoly = ((algSat 2 q {x, y}).map fun b => X - C b).prod) : M.det = (q : ℂ) * ((x * y : ℂˣ) : ℂ) := by
  have hq : ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) * ((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2)) = q := by
    rw [← Real.rpow_add' (Nat.cast_nonneg q) (by norm_num)]
    norm_num
  have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hq'
  have e : algSat 2 q {x, y} = {(((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * x,
      (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * y} := by
    simp [algSat]
  rw [Matrix.det_eq_prod_roots_charpoly, h, roots_multiset_prod_X_sub_C, e, Multiset.prod_pair, mul_mul_mul_comm, hq',
    Units.val_mul]
private theorem gap_of_sum {x y : ℂ} (hne : x ≠ y) {i j : ℤ} (hi : x = i + 1 / 2) (hj : y = j + 1 / 2) (hs : x + y = 1) :
    ∃ (c : ℂ) (k : ℕ), 2 ≤ k ∧ ({x, y} : Multiset ℂ) = {c, c + k} := by
  have h0 : i + j = 0 := by
    have : ((i + j : ℤ) : ℂ) = 0 := by push_cast; linear_combination hs - hi - hj
    exact_mod_cast this
  have h1 : i ≠ j := fun e => hne (by rw [hi, hj, e])
  rcases lt_or_gt_of_ne h1 with h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨x, k, by omega, ?_⟩
    have : ((j - i : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show x + k = y by linear_combination hi - hj - this]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    refine ⟨y, k, by omega, ?_⟩
    have : ((i - j : ℤ) : ℂ) = k := by rw [hk]; simp
    push_cast at this
    rw [show y + k = x by linear_combination hj - hi - this, Multiset.pair_comm]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.gapTwo_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Bc.GapTwo := by
  intro _ F Ω _ _ _ _ _ _ l _ ι r P hreg hatt ⟨N, hN, hdet⟩ τ
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral F 2 P
  have hone : (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) ^ N = 1 := by
    refine PositivityTheory.jumpWindows.FiniteInfinitePlaceProduct.eq_one _ ?_
    filter_upwards [hatt.2] with w ⟨B, hB, hF⟩
    obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hB.card
    have h1 := PositivityTheory.jumpWindows.PSmo.val_eq_prod (CuspSub.hasCentral_iff.1 hω) hB
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have e2 := (hF A hA).2 σ hσ
    rw [← Matrix.charpoly_map] at e2
    have e3 := det_algSat _ _ _ _ e2
    have e4 : ι (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom).det := ι.toRingHom.map_det _
    have e5 := congrArg (fun u : (Qbar l)ˣ => ι (u : Qbar l)) (hdet σ⁻¹)
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, Matrix.GeneralLinearGroup.val_det_apply] at e5
    rw [e4, e3] at e5
    have e6 := (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (-1)).2.1 w
    refine Units.ext ?_
    have hp : ∀ ν : HChar F, (ν ^ N).val w = ν.val w ^ N := fun ν => MonoidHom.pow_apply ν.1 N _
    rw [hp, HChar.val_mul, Units.val_pow_eq_pow_val, Units.val_mul, e6, h1, Multiset.prod_pair, Units.val_one, ← e5, mul_comm]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsum : ((CG.mk P).infChar τ).sum = 1 := by
    have h1 := GlobalTheory.BCT.TwistDisc.expo_pow (ω * GlobalTheory.HeckeGal.Model.absPow F (-1)) N τ
    have h2 := GlobalTheory.BCT.TwistDisc.expo_pow (1 : HChar F) 0 τ
    rw [pow_zero, Nat.cast_zero, zero_mul] at h2
    have h3 := (CG.hasInfChar_ofChar ω τ).twist (GlobalTheory.HeckeGal.Model.absPow F (-1))
    rw [CG.twist_ofChar, Multiset.map_singleton] at h3
    have h4 := h3.infChar_eq
    rw [CG.infChar_ofChar, Multiset.singleton_inj] at h4
    have h5 : expo (GlobalTheory.HeckeGal.Model.absPow F (-1)) τ = ((-1 : ℝ) : ℂ) := GlobalTheory.CuspRep.Model.expo_absC _ τ
    rw [hone, h2, h4, h5, expo_central hω (ParLaws.hasInfChar_infChar (CG.mk P) τ)] at h1
    have h6 := (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hN.ne')
    push_cast at h6
    linear_combination h6
  have hm : P.HasInfChar τ ((CG.mk P).infChar τ) := ParLaws.hasInfChar_infChar (CG.mk P) τ
  obtain ⟨hnd, hint⟩ := hreg τ
  obtain ⟨x, y, e⟩ := Multiset.card_eq_two.1 (CG.card_infChar (CG.mk P) τ)
  rw [e] at hm hnd hint hsum
  obtain ⟨i, hi⟩ := hint x (by simp)
  obtain ⟨j, hj⟩ := hint y (by simp)
  obtain ⟨c, k, hk, e'⟩ := gap_of_sum (x := x) (y := y) (by simpa using hnd) (i := i) (j := j) (by rw [hi]; norm_num)
    (by rw [hj]; norm_num) (by simpa using hsum)
  exact ⟨c, k, hk, e' ▸ hm⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open UpperTheory.V UpperTheory.V.Af
open scoped Matrix
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
local instance (priority := high + 1)  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] :
    Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
private theorem cofinite_notMem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw
private theorem mem_of_normV_dvd {N : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (h : normV w ∣ N) :
    ((N : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  obtain ⟨c, rfl⟩ := h
  have e : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [Nat.cast_mul, e]
  exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
private theorem charpoly_scale {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂ)
    (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by linear_combination e0
  have ht : φ M.trace = x + y := by linear_combination e0 - e1
  simp only [hd, ht, C_add, C_mul]
  ring
private theorem scale_sat {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (B : Multiset ℂˣ) (q : ℕ)
    (u : ℂˣ) (hu : φ c = u) (P Q : ℂ[X]) (h : M.charpoly.map φ = P)
    (hP : ((algSat 2 q B).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = P)
    (hQ : ((algSat 2 q (B.map (· * u))).map fun b => X - C ((q : ℂ) ^ (0 : ℤ) * b)).prod = Q) :
    (c • M).charpoly.map φ = Q := by
  simp only [zpow_zero, one_mul] at hP hQ
  rw [charpoly_scale φ M c (algSat 2 q B) (h.trans hP.symm), ← hQ, hu]
  simp only [algSat, Multiset.bind_singleton, Multiset.map_map, Multiset.pure_def, Multiset.bind_def]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply, Units.val_mul]
  ring_nf
private theorem ss_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 hW', hc⟩
private theorem isOpen_ker {Ω C : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Group C] {N : ℕ} (hN : 1 ≤ N)
    {κ : G ℚ Ω →* C} (hκ : KillsMu N κ) : IsOpen (κ.ker : Set (G ℚ Ω)) := by
  have hfin : {ζ : Ω | ζ ^ N = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hN] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := ℚ) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hκ s fun ζ hζ => hs ζ hζ
theorem exists_newform_attached_twist_of_kills_mu (P : _root_.UpperTheory.V.Af.HypothesesH') {k : ℕ} (hk : 2 ≤ k) (f : Newform k) {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hf : f.Att ι V)
    (κ : G ℚ Ω →* (Qbar l)ˣ) {N : ℕ} (hN : 1 ≤ N) (hκ : KillsMu N κ) :
    ∃ g : Newform k, g.Att ι (tw V κ) := by
  obtain ⟨art, ha⟩ : ∃ art : Neutral.B1.Ideles ℚ →* Gab ℚ Ω, IsGlobalArtin art := P.toClassicalTheorems.litN.aut.art _ Ω
  have ho := isOpen_ker hN hκ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfi : Finite (G ℚ Ω ⧸ κ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hm : 0 < κ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι κ (continuous_of_isOpen_ker' κ ho) hm
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact κ.ker.pow_index_mem s)
  have hexpo : ∀ v, TR.expo χ v = 0 := GlobalTheory.HenQ.expo_eq_zero_of_pow χ hm h1
  obtain ⟨π, hinf, hsat⟩ := P.toClassicalTheorems.newform k hk f 0
  obtain ⟨g, hg⟩ := UpperTheory.V.Af.repNewform k hk 0 (π.twist χ) fun v => by
    have := (hinf v).twist χ
    rw [hexpo v] at this
    simpa using this
  refine ⟨g, ss_twist _ _ hf.1, ?_⟩
  filter_upwards [hf.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ), cofinite_notMem l hl.out.ne_zero,
    cofinite_notMem f.M f.pos.ne', cofinite_notMem g.M g.pos.ne'] with w hw hu hwl hwf hwg A hA
  obtain ⟨B, hB, hpB⟩ := hsat w fun h => hwf (mem_of_normV_dvd h)
  obtain ⟨S, hS, hpS⟩ := hg w fun h => hwg (mem_of_normV_dvd h)
  obtain rfl : S = B.map (· * χ.val w) := hS.unique (hB.twist hu)
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have e1 : κ s = 1 := (hL.unr_iff ha (Or.inl hwl) hA).2 hu s hs
    apply Units.ext
    rw [tw_val, e1, (hw A hA).1 s hs, Units.val_one, one_smul, Units.val_one]
  · have e1 : ι.toRingHom ((κ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (χ.val w : ℂ) := by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inl hwl) hu hA hσ, inv_inv]
      exact ι.apply_symm_apply _
    rw [tw_val]
    exact scale_sat ι.toRingHom _ _ B _ _ e1 _ _ ((hw A hA).2 σ hσ) hpB hpS
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ := by
  intro P l _ Ω _ _ _ ι e W _ he hA M φ hM hφ
  obtain ⟨f, M', φ', hM', hφ', hf⟩ := hA.modular
  have hMM : 1 ≤ M * M' := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hκ : KillsMu (M * M') (φ * φ'⁻¹) := fun s hs => by
    have h1 : φ s = 1 := hφ s fun ζ hζ => hs ζ (by rw [pow_mul, hζ, one_pow])
    have h2 : φ' s = 1 := hφ' s fun ζ hζ => hs ζ (by rw [mul_comm, pow_mul, hζ, one_pow])
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, one_mul]
  obtain ⟨g, hg⟩ := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistNewform.exists_newform_attached_twist_of_kills_mu P (by omega) f ι _ hf (φ * φ'⁻¹) hMM hκ
  refine ⟨g, ?_⟩
  convert hg using 1
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul]
  congr 2
  rw [mul_comm (φ s) (φ' s)⁻¹, mul_assoc, ← mul_assoc (φ s), mul_comm _ (φ' s), inv_mul_cancel_left, mul_comm]
end
end
end

section




section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th UpperTheory.V.Z.J UpperTheory.V.U3 UpperTheory.V.UnitaryThreeInertia UpperTheory.V.Alg UpperTheory.V.Aut
section Local
open Matrix IsLocalRing
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
end Local
private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]
open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Ua5.matIrr_conj h e H
private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  obtain ⟨m, rfl⟩ := hM.two_dvd
  have h2 : B.valuation ((2 : ℕ) : Ω) < 1 := by
    by_contra h2
    rw [not_lt] at h2
    rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.cast_mul, map_mul] at h
    exact absurd h (not_lt.2 (one_le_mul h2 h2))
  have hm : B.valuation (m : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B m)
  rw [Nat.cast_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hm) h2
private theorem unl_of_iso {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {n : ℕ} {M : ℕ} {m : Fin n → ℤ} {r r' : Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)}
    (H : Unl l M m r) (h : Af.RepIso r r') : Unl l M m r' := fun w hw => by
  obtain ⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, h4⟩ := H w hw
  exact ⟨A, hA, κ, ⟨χ, h1, h2.of_iso h, h3⟩, h4⟩
theorem UpperTheory.V.Z.J.hostUnlE_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UnlEndLogNorm → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F → ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r → U3.TypeI F.η r → ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), (∀ s : G K Ω, (ρ s).val = (r (toGS Ω _ (s.restrictScalars ℚ))).mat) → Unl l N ![(e : ℤ), 0, -(e : ℤ)] ρ := by
  intro hH hU K _ _ _ hK Ω _ _ _ _ _ l hl c N _ e ψ o₁ hd S A F hF g₁ hg r hr hI ρ hρ
  have hN := hH.litN
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  have ok := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  obtain ⟨hmu, -, -, -⟩ := isCharZeroPt_basic F ok g₁ hg r hr
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := by
    open Formalism.GaloisCohomology UpperTheory.V.Base in
    exact (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨σ, hσ, hσc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  have hfr := Fr.host_ex ⟨⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.pt⟩, hN.coh.uo, hN.coh.gw⟩
    Ω l c N e ψ o₁ hd σ hσ _ hv
  have hσ' : IsConjOm σ.toRingEquiv := hσ
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
    have h1 : cycZ ℚ Ω l σ = -1 := hσ'.cyc (E := ℚ)
    have h2 : Base.chiO ℚ Ω l c.O σ = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l σ) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ σ : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 σ hσ', MulChar.coe_toUnitHom]
      exact hd.par
    apply Units.ext
    show ((Base.chiO ℚ Ω l c.O σ ^ (e : ℤ) * Chr.dirG ℚ Ω ψ σ : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ (UnitaryThreeInertia.eta4 Ω).ker →
      B'.valuation ((l * N : ℕ) : Ω) < 1 := by
    intro B' h
    refine val_of_even B' (hd.N_even.mul_left l) ?_
    by_contra h4
    refine h fun s hs => ?_
    have h5 : Chr.cls ℚ Ω 4 s = 1 := (Chr.clsFacts ℚ Ω 4).2.2.2.2 B' h4 hs
    rw [MonoidHom.mem_ker, UnitaryThreeInertia.eta4, Chr.dirG, MonoidHom.comp_apply, h5, map_one]
  have hk : Pr.LinkHyp c N e (UnitaryThreeInertia.eta4 Ω) σ (A F.vl) (l * N) :=
    ⟨hd.e_pos, dvd_rfl, mul_ne_zero hl.out.ne_zero (NeZero.ne N), hram, hv, hσ⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlev := UnitaryThreeInertia.levelAt_of_pt Ω c e ψ o₁ hd S A F hF K hK g₁ hg r hr ρ hρ
  have hopen := UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF g₁ hg r hr hI
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hr
  obtain ⟨g, rfl⟩ : ∃ g, toGS Ω _ g = g₁ := QuotientGroup.mk_surjective g₁
  rw [hF.π] at hσc
  have ho := Pr.ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g hσc r' hr'
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s => (hmu _).trans (hη s)
  have hle : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  have hrg := (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← hrg]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => by
    rw [show ρ s = (r (toGS Ω _ (Base.galEmb ℚ K Ω s))).left from Units.ext (hρ s)]
    exact hle _ (hker s)⟩
  have key := hU Ω l c N e ψ (UnitaryThreeInertia.eta4 Ω) σ g (A F.vl) _ hk hd.N_even hΨ hfr B _ ho
    (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, GG.mat, GG.mat, hle s (hVη hs), ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) (hopen V hV hVη)) K hK.1 (by rw [← Base.range_galEmb]; exact hrg.symm) ρ' (fun s => rfl)
    N NeZero.one_le (hlev.of_iso hiso)
  exact unl_of_iso key (Af.RepIso.symm' hiso)
end
end

section




section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.GalN.V.autKQ0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ), Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G ℚ Ω)) → AutP ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : _root_.Formalism.ConjugateSelfDual.G K Ω →* _root_.Formalism.ConjugateSelfDual.G ℚ Ω)) := by
  intro hP K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r wt hc hr ⟨θ, hθ, hd⟩ hirr
  obtain ⟨P, hreg, hA⟩ := hr hc K hK hirr
  obtain ⟨χ, -, hpol, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP.toClassicalTheorems K hK n hn l Ω ι r wt θ P hθ hd hA
  exact ⟨P, hreg, ⟨χ, hpol⟩, hA⟩
end
end
