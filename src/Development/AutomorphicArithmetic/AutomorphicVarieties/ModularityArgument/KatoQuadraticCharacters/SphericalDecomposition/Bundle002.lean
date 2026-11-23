module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle294
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle032
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ConjAlgebraMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfUseN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle001
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩

private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* H} {s : _root_.Formalism.ConjugateSelfDual.G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩

private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], ?_, ?_⟩, fun s => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two]
  · have e : (r s : Matrix (Fin 2) (Fin 2) k) = !![(r s : Matrix (Fin 2) (Fin 2) k) 0 0, (r s : Matrix (Fin 2) (Fin 2) k) 0 1;
        (r s : Matrix (Fin 2) (Fin 2) k) 1 0, (r s : Matrix (Fin 2) (Fin 2) k) 1 1] := Matrix.eta_fin_two _
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.coe_units_inv]
    rw [e, Matrix.det_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem polar_of_lift (hP : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (hK : Module.finrank ℚ K = 2)
    {l : ℕ} [Fact l.Prime] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (wt : ℤ) (θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ 2)
    (Q : CuspSub K 2) (hBC : Br.IsBC0 π Q) (hC : AttC ι (r.comp (Bc.res ℚ Ω K)) Q) (hθ : IsCycWt l wt θ) (hd : DualTw r θ) :
    ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ := by
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  have hθ' : IsCycWt l (wt + (((2 : ℕ) : ℤ) - 1))
      (θ.comp (Bc.res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ (((2 : ℕ) : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (Bc.res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL 2
  have hres' : μ'.comp (Bc.res (maximalRealSubfield K) Ω K) =
      θ.comp (Bc.res ℚ Ω K) * cycBar K Ω l ^ (((2 : ℕ) : ℤ) - 1) := hres.trans rfl
  refine ⟨χ', hs, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hP.litN.aut.js.1 hP.litN.aut.gk K 2 one_le_two Q _ ?_⟩
  have hd' : DualTw (r.comp (Bc.res ℚ Ω K)) (θ.comp (Bc.res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  filter_upwards [Bc.normGal K Ω l ι χ' μ' hL', Br.bcConj0 ℚ K 2 π Q hBC, hC.2, hl] with w ⟨hu, he⟩ ⟨B, hB, hB'⟩ ⟨B₁, hB₁, hF⟩ hw
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι 2 _ _ hd' w hw B _ hF he⟩

private theorem qV_eq {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Formalism.UG.qV E w = Ideal.absNorm w.asIdeal := by
  rw [Formalism.UG.qV]

private theorem absNorm_rat {l : ℕ} (hp : l.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = l := by
  have hN : Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hd : Ideal.absNorm v.asIdeal ∣ l :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hv)
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact v.isPrime.ne_top

private theorem sat_iff (hP : Hypotheses₂) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Algebra ℚ K]
    (π : TR.CuspSub ℚ 2) (Q : CuspSub K 2) (hBC : IsBC π Q) (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion ℚ ≃+* w.adicCompletion K) (hi : IsCompl i) (B : Multiset ℂˣ) :
    π.HasSat v B ↔ (CG.mk Q).HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR hP ℚ 2 π v
  obtain ⟨⟨σ', hσ'⟩, hiso'⟩ := locCompC hP K 2 Q w
  have hc := hi.1
  obtain ⟨e, he⟩ := hBC.split v w i hi.1 hi.2 σ σ' hσ hσ'
  have c1 := (satLoc hP ℚ 2 v σ).2 _ π.finPart (hiso σ hσ) B
  have c2 := (satLoc hP K 2 w σ').2 _ Q.finPart (hiso' σ' hσ') B
  have hq : Formalism.UG.qV K w = Formalism.UG.qV ℚ v := by
    rw [qV_eq, qV_eq, GlobalTheory.LiftAbsPow.absNorm_eq i hc]
  refine ⟨fun hB => (CG.hasSat_mk _ _ _).2 (c2.2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i (GlobalTheory.LiftAbsPow.v_map_eq i hc) hq e
    (fun g x => (he g x).symm) (c1.1 hB))), fun hB => c1.2 ?_⟩
  refine GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i.symm (fun y => ?_) hq.symm e.symm (fun g x => ?_) (c2.1 ((CG.hasSat_mk _ _ _).1 hB))
  · have := GlobalTheory.LiftAbsPow.v_map_eq i hc (i.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
    congr 2
    exact (Units.ext (Matrix.ext fun _ _ => (i.apply_symm_apply _)) :
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g)

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness

private theorem irr_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (h : IsIrr (tw r φ)) : IsIrr r := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun U _ hU => hmin U le_top fun s v hv => ?_⟩
  have e : (tw r φ s : Matrix (Fin n) (Fin n) k).mulVec v =
      (φ s : k) • (r s : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec]
  rw [e]
  exact U.smul_mem _ (hU s v hv)

private theorem comp_tw {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (f : Δ →* Γ) : (tw r φ).comp f = tw (r.comp f) (φ.comp f) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp only [MonoidHom.comp_apply, tw_val]

private theorem open_ker {K Ω C : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [Algebra ℚ K] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] [Group C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C}
    (hφ : KillsMu M φ) :
    IsOpen ((φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).ker : Set (G K Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ _ fun ζ hζ => hs ζ hζ

end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness

end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
open UpperTheory.V UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  exact ⟨_, eq_unrChar h hϖ⟩

private theorem unr_eq {a b : ℂˣ} (h : (a : ℂ) = (resCard k : ℂ) * b) : unrChar k b = unrChar k a * absPow k 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hU : IsUnram (unrChar k a * absPow k 1) := fun u hu => by
    rw [MonoidHom.mul_apply, isUnram_unrChar k a u hu, isUnram_absPow k 1 u hu, one_mul]
  rw [eq_unrChar hU hϖ]
  congr 1
  refine Units.ext ?_
  simp only [MonoidHom.mul_apply, Units.val_mul]
  rw [unrChar_uniformizer k a hϖ, val_absPow, Complex.cpow_one, h]
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [hn]
  push_cast
  field_simp

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_of_level {n : ℕ} {x : WD h} (hL : IsLevelWD 1 n x) : x.unr := by
  obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
  have h1 : ((1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    rw [Nat.cast_one]
    exact fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rw [← e, WD.unr_mk]
  refine ⟨hN, fun s => ?_⟩
  rw [hb s]
  simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char E Ω w A h 1 h1 s s.2), Module.End.one_eq_id]

private theorem eq_one_of_root {x : WD h} (hu : x.unr) (t : Ine (F := E) A) {z : ℂ}
    (hz : (x.charPol (ineIncl h t)).IsRoot z) : z = 1 := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  exact smul_left_injective ℂ hv.2 (by simpa using h3.symm)

end WD

end UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

end
end
