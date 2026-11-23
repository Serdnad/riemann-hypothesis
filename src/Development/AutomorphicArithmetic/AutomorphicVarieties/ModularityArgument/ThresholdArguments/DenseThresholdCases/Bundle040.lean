module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle021
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExLLeOfCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPropMV
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (_root_.Formalism.ConjugateSelfDual.G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → ∀ σ : _root_.Formalism.ConjugateSelfDual.G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w ∧ ∃ σ ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add (f := _)]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add (f := _), map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
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
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J.D
private theorem val_eq {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {F : M} (h0 : F ≠ 0) {a b : ℂ}
    (h : T F = a • F) (hg : F ∈ T.maxGenEigenspace b) : a = b := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T b F).1 hg
  have hp : ∀ k : ℕ, ((T - b • (1 : Module.End ℂ M)) ^ k) F = (a - b) ^ k • F := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ]
  rw [hp k] at hk
  rcases smul_eq_zero.1 hk with h1 | h1
  · exact sub_eq_zero.1 (by_contra fun h2 => pow_ne_zero k h2 h1)
  · exact absurd h1 h0
private theorem chi_map {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (D : W.GDet n R G) (f : R →+* S) (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra R (Polynomial S) := ((algebraMap S (Polynomial S)).comp f).toAlgebra
  let φ : Polynomial R →ₐ[R] Polynomial S :=
    { Polynomial.mapRingHom f with commutes' := fun b => Polynomial.map_C f }
  refine Eq.trans ?_ (D.nat (Polynomial R) (Polynomial S) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1)))
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem pol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n q : ℕ) (a : ℕ → R) (b : ℕ → S)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol

  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem ss_irr {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
theorem partRep_s : _root_.UpperTheory.V.Z.J.D.PartRepAlt := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι x lam d ξ c0 sp _ K a _ _ _ z _ I D ψ hU ρ hρ hirr hD Y hY
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  have hgen : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ι (z (H.gen θ a K i))) := fun i =>
    (Submodule.mem_iInf _).1 hF.2.2 i
  have hval : ∀ (w : H.Wp) (j : ℕ), j ≤ n → ι (z (H.genW θ a K w j)) = Y.a w j := by
    intro w j hj
    unfold HSet.genW
    split_ifs with h
    · have e := Y.sph w (j - 1 + 1) F hF.1
      rw [show j - 1 + 1 = j by omega] at e
      have e' : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = Y.a w j • F := by
        have e2 : H.opC ι lam d (.inl (w, ⟨j - 1, h.2⟩)) F = sphOp (H.atW ι d w.1) (j - 1 + 1) F := rfl
        rw [e2, show j - 1 + 1 = j by omega, e]
      exact (val_eq _ hF0 e' (hgen _)).symm
    · rw [show j = 0 by omega, Y.a_zero, map_one, map_one]
  have e : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat ρ) := by
    refine AlgebraTools.Det.extDense _ _ _ hH.dense (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i)
      (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hρ) i) ?_
    rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [← hD, chi_map, hU.frob ⟨w, hw⟩ B σ hB hσ, (AlgebraTools.Det.repApi _).2.1]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    refine (Y.frob ⟨w, hw⟩ B σ hB hσ).trans ?_
    rw [Polynomial.map_map]
    exact (pol_map _ n _ _ _ fun j hj => hval ⟨w, hw⟩ j hj).symm
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat ρ) Y.ss (ss_irr hirr) fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat Y.r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
end UpperTheory.V.Z.J.D
end
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_place_above_prime_bis (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem trace_map_ring_hom {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (y : MonoidAlgebra A G) : (D.map f).tr (MonoidAlgebra.mapRingHom G f y) = f (D.tr y) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 1
private theorem trace_map_comp {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : GDet n A G)
    (f : A →+* B) (g : B →+* C) (k : A →+* C) (hk : g.comp f = k) (y : MonoidAlgebra B G) :
    g ((D.map f).tr y) = (D.map k).tr (MonoidAlgebra.mapRingHom G g y) := by
  rw [← trace_map_ring_hom, (UpperTheory.V.CA.d_gmap D).2.1, hk]
private theorem charpoly_of_representation {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y : MonoidAlgebra K G) : (GDet.ofRep ρ).chi y = (GDet.repAlg ρ K y).charpoly := by
  change (GDet.repAlg ρ (Polynomial K) _).det = Matrix.det _
  congr 1
  have h : GDet.repAlg ρ (Polynomial K) (MonoidAlgebra.mapRingHom G Polynomial.C y) =
      (Polynomial.C : K →+* Polynomial K).mapMatrix (GDet.repAlg ρ K y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]
  rw [map_sub, h, Matrix.charmatrix]
  congr 1
  exact (GDet.repAlg ρ (Polynomial K)).commutes Polynomial.X
private theorem trace_eq_zero_of_rep_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y₀ y : MonoidAlgebra K G) (h₀ : (GDet.ofRep ρ).tr y₀ = 0) (h : GDet.repAlg ρ K y = 0) : (GDet.ofRep ρ).tr y = 0 := by
  rcases n with _ | n
  · rw [← h₀, GDet.tr, GDet.tr, GDet.lam, GDet.lam, charpoly_of_representation, charpoly_of_representation, Subsingleton.elim (GDet.repAlg ρ K y) (GDet.repAlg ρ K y₀)]
  · nontriviality K
    rw [GDet.tr, GDet.lam, charpoly_of_representation, h, Matrix.charpoly_zero, Polynomial.coeff_X_pow]
    simp
private theorem map_ring_hom_first_relation {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (g ph : G) (u : Fin n → A) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q1El ph u) = MonoidAlgebra.single g 1 * q1El ph fun i => f (u i) := by
  simp only [q1El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
private theorem map_ring_hom_second_relation {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (g ph ta : G) (u : Fin n → A)
    (i : Fin n) (y : A) : MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g 1 * q2El ph ta u i y) =
      MonoidAlgebra.single g 1 * q2El ph ta (fun i => f (u i)) i (f y) := by
  simp only [q2El, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, apply_ite (MonoidAlgebra.mapRingHom G f),
    MonoidAlgebra.mapRingHom_single, map_one]
private theorem rep_single_eq_smul {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g : G) (a : K) :
    GDet.repAlg ρ K (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]
private theorem rep_first_relation_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g ph : G)
    (α : Fin n → K) (h : (ρ ph).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    GDet.repAlg ρ K (MonoidAlgebra.single g 1 * q1El ph α) = 0 := by
  have h1 := Matrix.aeval_self_charpoly (ρ ph)
  rw [h, ← List.prod_ofFn, map_list_prod, List.map_ofFn] at h1
  rw [map_mul, q1El, map_list_prod, List.map_ofFn]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h1)
  congr 2
  funext i
  simp [rep_single_eq_smul, Algebra.algebraMap_eq_smul_one]
private theorem rep_second_relation_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g ph ta : G)
    (α : Fin n → K) (i : Fin n) (c : K)
    (h : (List.ofFn fun i' => if i' = i then 1 else ρ ph - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod *
      (ρ ta - c • (1 : Matrix (Fin n) (Fin n) K)) = 0) :
    GDet.repAlg ρ K (MonoidAlgebra.single g 1 * q2El ph ta α i (c - 1)) = 0 := by
  rw [map_mul, q2El, map_mul, map_list_prod, List.map_ofFn]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  congr 1
  · congr 2
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single_eq_smul]
  · simp [rep_single_eq_smul, sub_smul]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem reduction_of_polynomial_element {n q : ℕ} {R G E : Type} [CommRing R] [Group G] [Ring E] [Algebra R E] (D : GDet n R G)
    (act : PUY R q n →ₐ[R] E) (Nq : Fin q → ℕ) (j : Fin q) (k : ℕ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (z' : MonoidAlgebra (PUY R q n) G)
    (hz : MonoidAlgebra.mapRingHom G (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom z = z')
    (h : act (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))
      ((∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, ((MvPolynomial.X (.inl i) - MvPolynomial.X (.inl i')) *
        (MvPolynomial.X (.inl i) - (Nq j : MvPolynomial (Fin n ⊕ Fin n) R) * MvPolynomial.X (.inl i')))) *
        (D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) ^ k) = 0) :
    act ((fEl Nq (uV R) * (D.map (MvPolynomial.C : R →+* PUY R q n)).tr z') ^ k) = 0 := by
  have e := trace_map_comp D (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom MvPolynomial.C (by ext : 1; simp) z
  rw [hz] at e
  rw [fEl, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_assoc, mul_pow, map_mul, ← e]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  simp [map_prod]
private theorem trace_vanishing_of_evaluation {n : ℕ} {R K G : Type} [CommRing R] [CommRing K] [Group G] (D : GDet n R G) (θ : R →+* K) (ι : K →+* ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map θ = GDet.ofRep ρ) (z₀ : MonoidAlgebra R G) (h₀ : D.tr z₀ = 0)
    (v : Fin n ⊕ Fin n → ℂ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (h : GDet.repAlg (ι.mapMatrix.toMonoidHom.comp ρ) ℂ
      (MonoidAlgebra.mapRingHom G (MvPolynomial.eval₂Hom (ι.comp θ) v) z) = 0) :
    MvPolynomial.eval₂ (ι.comp θ) v ((D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) = 0 := by
  have hD' : D.map (ι.comp θ) = GDet.ofRep (ι.mapMatrix.toMonoidHom.comp ρ) := by
    rw [← (UpperTheory.V.CA.d_gmap D).2.1, hD, (UpperTheory.V.CA.d_gmap (GDet.ofRep ρ)).2.2.2]
  rw [← MvPolynomial.coe_eval₂Hom, trace_map_comp D _ _ (ι.comp θ) (by ext : 1; simp), hD']
  refine trace_eq_zero_of_rep_eq_zero _ (MonoidAlgebra.mapRingHom G (ι.comp θ) z₀) _ ?_ h
  rw [← hD', trace_map_ring_hom, h₀, map_zero]
theorem UpperTheory.V.Z.Win.T2.level_relation_one_two :
    _root_.UpperTheory.V.Pa.Lev.LevelRelationOneTwo := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ h1 h2 h3 T ph ta ⟨ι, hsep, hloc⟩
  obtain ⟨v⟩ : Nonempty (globOf r V).frame.Vl := (exists_place_above_prime_bis (Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  have h₀ := A.p.Ord v (fun _ => 1) 1
  refine ⟨fun j g => ?_, fun j i g => ?_⟩
  · refine reduction_of_polynomial_element A.p.D T.act1 (qj w) j _ (MonoidAlgebra.single g 1 * q1El (ph j) fun i => MvPolynomial.X (.inl i)) _
      ((map_ring_hom_first_relation _ _ _ _).trans (by simp)) ?_
    refine _root_.UpperTheory.V.Pa.Lev.relOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ => ?_
    rw [MvPolynomial.eval₂_mul]
    refine mul_eq_zero.2 (or_iff_not_imp_left.2 fun hne => ?_)
    refine trace_vanishing_of_evaluation A.p.D y.θ ι.toRingHom (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_first_relation]
    refine rep_first_relation_eq_zero _ _ _ _ ?_
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl]
    refine (_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).1 (Or.inr fun a a' ha => ?_)
    rw [← MvPolynomial.coe_eval₂Hom] at hne
    simp only [map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl] at hne
    have h4 := Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne a (Finset.mem_univ _)) a'
      (Finset.mem_erase.2 ⟨ha.symm, Finset.mem_univ _⟩)
    exact ⟨sub_ne_zero.1 (left_ne_zero_of_mul h4), sub_ne_zero.1 (right_ne_zero_of_mul h4)⟩
  · refine reduction_of_polynomial_element A.p.D T.act1 (qj w) j _
      (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (fun i => MvPolynomial.X (.inl i)) i (MvPolynomial.X (.inr i))) _
      ((map_ring_hom_second_relation _ _ _ _ _ _ _).trans (by simp)) ?_
    refine _root_.UpperTheory.V.Pa.Lev.relOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ => ?_
    rw [MvPolynomial.eval₂_mul]
    refine mul_eq_zero.2 (or_iff_not_imp_left.2 fun hne => ?_)
    refine trace_vanishing_of_evaluation A.p.D y.θ ι.toRingHom (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_second_relation]
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    refine rep_second_relation_eq_zero _ _ _ _ _ _ _ ((_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).2 (fun a a' ha => ?_) i)
    rw [← MvPolynomial.coe_eval₂Hom] at hne
    simp only [map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl] at hne
    have h4 := Finset.prod_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 hne a (Finset.mem_univ _)) a'
      (Finset.mem_erase.2 ⟨ha.symm, Finset.mem_univ _⟩)
    exact ⟨sub_ne_zero.1 (left_ne_zero_of_mul h4), sub_ne_zero.1 (right_ne_zero_of_mul h4)⟩
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr
open UpperTheory.GalN.V
theorem UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.AdmResNAlt := by
  intro hP K _ _ _ hK n hn m wt hm M hM l _ hl Ω _ _ _ _ _ _ ι r hr hirr
  have hC := Lev.LevelF.of_level hr.level
  have hF := Lev.levelFRes ℚ K Ω l n M m r hC
  obtain ⟨⟨P, hreg, hA⟩, hW⟩ := hr.aut hC.cont K hK hirr
  obtain ⟨θ, hθ, hd⟩ := hr.dual
  obtain ⟨χ, μ, hpol, -, -⟩ := _root_.UpperTheory.V.Z.Bc.polarization_k_of_printed_results hP K hK n (by omega) l Ω ι r wt θ P hθ hd hA
  exact ⟨hirr, ⟨P, hreg, ⟨χ, hpol⟩, hA⟩, hW, hF, _root_.UpperTheory.V.Z.Win.A4.safeRes' K (_root_.UpperTheory.V.Z.Win.A4.safeUP'_alt hP hr.irr hr.level hr.aut hr.safe)⟩
end
end
end
