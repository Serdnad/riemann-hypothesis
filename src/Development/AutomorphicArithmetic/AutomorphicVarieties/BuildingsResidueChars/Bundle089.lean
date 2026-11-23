module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Lean.Meta.ExprDefEq

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder :
    UpperTheory.V.Af.Sol.FrobDualC → UpperTheory.V.Af.Sol.ConjUnder → UpperTheory.V.Af.Sol.DualBcC := by
  intro hF hU K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π sat' huniq hbc hatt μ χ c P hL hc hpair
  obtain ⟨j, hj⟩ := hc
  let c' : _root_.Formalism.ConjugateSelfDual.G (maximalRealSubfield M) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap M Ω))
  have hpair' : IsPairing c' (r.comp (resG K M Ω)) (cycBar M Ω l ^ (1 - (n : ℤ)) *
      (μ.comp (resG (maximalRealSubfield K) K Ω)).comp (resG K M Ω)) P := fun s s' hs =>
    hpair (resG K M Ω s) (resG K M Ω s') (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have h0 : Ideal.span {((l : ℕ) : 𝓞 M)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ((l : ℕ) : 𝓞 M) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have ht := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite
  filter_upwards [hbc, ht.eventually hbc, hatt.2, ht.eventually hatt.2, hl,
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (Bc.normGal K Ω l ι χ μ hL)]
    with w h1 h2 ⟨C, hC, hE⟩ ⟨C', hC', hE'⟩ hw ⟨hu, he⟩ f hf
  obtain ⟨e1, e2, -⟩ := hU K M w
  obtain ⟨-, e3, -⟩ := hU K K (w.under (𝓞 K))
  obtain ⟨B, hB, hs⟩ := h1 f hf
  obtain ⟨B', hB', hs'⟩ := h2 f (by
    change normV (cPl w) = normV ((cPl w).under (𝓞 K)) ^ f
    rw [e2, e1, e3, hf])
  obtain rfl := huniq _ _ _ hs hC
  obtain rfl := huniq _ _ _ hs' hC'
  have he' := (UpperTheory.frobenius_power_compatibility K M Ω l ι w f hf).2 _ _ he
  rw [← Units.val_pow_eq_pow_val] at he'
  have key := hF M Ω l ι n _ _ c' P ⟨j, hj⟩ hpair' w hw _ _ _ hE hE' he'
  have hB'' : (CG.mk π).HasSat (cPl (w.under (𝓞 K))) B' := e1 ▸ hB'
  have hT := UpperTheory.theta_satake_parameters_inverse K n π _ _ hB''
  rw [CG.hasSat_mk] at hT
  refine ⟨_, (CG.hasSat_mk ..).2 (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) _ _ hu hT), ?_⟩
  convert hs using 1
  have k2 := congrArg (Multiset.map (· * (compNorm K χ).val (w.under (𝓞 K)) ^ f)) key
  simp only [Multiset.map_map, Function.comp_def, inv_mul_cancel_right] at k2 ⊢
  rw [← k2]
  simp only [mul_pow, inv_pow]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.isoSum_of_injective_equivariant_family :
    ∀ (H M N : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (ρ : Representation ℂ H M) (ρ' : Representation ℂ H N) (Y : Submodule ℂ M) (Z : Submodule ℂ N) (τ : SmIrr H) (I : Type) [Finite I] (φ : I → M →ₗ[ℂ] N), IsoSum ρ' Z τ → (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → (∀ i, ∀ y ∈ Y, φ i y ∈ Z) → (∀ i g, ∀ y ∈ Y, φ i (ρ g y) = ρ' g (φ i y)) → (∀ y ∈ Y, (∀ i, φ i y = 0) → y = 0) → IsoSum ρ Y τ := by
  intro H M N _ _ _ _ _ _ _ ρ ρ' Y Z τ I _ φ hZ hY hφ he hinj
  classical
  let := Fintype.ofFinite I
  let π : Representation ℂ H Y := (⟨Y, fun g v hv => hY g v hv⟩ : Subrepresentation ρ).toRepresentation
  let P : Representation ℂ H (I → N) :=
    { toFun := fun g => (ρ' g).compLeft I
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let j : Y →ₗ[ℂ] (I → N) := LinearMap.pi fun i => φ i ∘ₗ Y.subtype
  have hj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hinj y y.2 fun i => congrFun hy i)
  have hs : ∀ i g x, LinearMap.single ℂ (fun _ : I => N) i (ρ' g x) = P g (LinearMap.single ℂ (fun _ : I => N) i x) := by
    intro i g x
    funext k
    change (Pi.single i (ρ' g x) : I → N) k = ρ' g ((Pi.single i x : I → N) k)
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  have hsing : ∀ i, ∀ z ∈ Z, LinearMap.single ℂ (fun _ : I => N) i z ∈
      ⨆ f : {f : τ.V →ₗ[ℂ] (I → N) // ∀ g v, f (τ.ρ g v) = P g (f v)}, LinearMap.range f.1 := by
    intro i z hz
    refine Submodule.iSup_induction _ (motive := fun z => LinearMap.single ℂ (fun _ : I => N) i z ∈ _) (hZ hz) ?_ ?_ ?_
    · rintro f _ ⟨s, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : I => N) i ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2.1, hs]; rfl⟩ ⟨s, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have key := UpperTheory.V.PiLin.iso_sub τ.ρ π P τ.irred j hj (fun g y => funext fun i => he i g y y.2) (fun y => by
    rw [← Finset.univ_sum_single (j y)]
    exact Submodule.sum_mem _ fun i _ => hsing i _ (hφ i y y.2))
  intro y hy
  refine Submodule.iSup_induction _ (motive := fun z : Y => (z : M) ∈ _) (key ⟨y, hy⟩) ?_ ?_ ?_
  · rintro f _ ⟨s, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨Y.subtype ∘ₗ f.1, fun g v => ?_, ?_⟩ ⟨s, rfl⟩
    · exact congrArg Subtype.val (f.2 g v)
    · rintro _ ⟨v, rfl⟩; exact (f.1 v).2
  · exact zero_mem _
  · intro a b ha hb
    exact add_mem ha hb
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ) (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (r : G L Ω →* GL (Fin n) (Qbar l)) (χ : Fin n → Ine (F := L) A →* (Qbar l)ˣ) (x : WD h), IsWDOf ι r x → IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x → ∃ g : GL (Fin n) (Qbar l), ∀ t : Ine (F := L) A, ((g * r t * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (χ i t : Qbar l) := by
  intro l _ L Ω _ _ _ _ _ ι n A w h _hl r χ x hWD hType
  classical
  obtain ⟨t, _ht, φ, hφ, N, a, hMon, hFS, hax⟩ := hWD
  obtain ⟨b, hbx, hbN, hbρ⟩ := hType
  have hiso : a.Iso b := WD.mk_eq_mk.mp (hax.trans hbx.symm)
  obtain ⟨e, he1, he2⟩ := hiso
  obtain ⟨_hNnil, U, hUo, hU⟩ := hMon
  obtain ⟨haN, hFS⟩ := hFS
  have htoEnd : ∀ X : Matrix (Fin n) (Fin n) (Qbar l),
      toEndC ι X = Matrix.toLin' (X.map ι) := fun X => rfl
  have haN0 : a.N = 0 := by
    apply LinearMap.ext
    intro v
    have h0 := he2 v
    rw [hbN, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h0
    exact h0
  have hN0 : N = 0 := by
    have h0 : Matrix.toLin' (N.map ι) = Matrix.toLin' (0 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← htoEnd, ← haN, haN0, map_zero]
    have h2 := Matrix.toLin'.injective h0
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa using h3
  have hpow : ∀ s : Ine (F := L) A, ∃ m : ℕ, 0 < m ∧ s ^ m ∈ U := by
    intro s
    have hUn : (U : Set (Ine (F := L) A)) ∈ nhds (1 : Ine (F := L) A) := hUo.mem_nhds U.one_mem
    obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).mp hUn
    obtain ⟨E, hEfin, hEu⟩ := (krullTopology_mem_nhds_one_iff L Ω u).mp hu
    let f : ℕ → (E →ₐ[L] Ω) := fun k => ((s : G L Ω) ^ k).toAlgHom.comp E.val
    obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
    have key : ∀ i j : ℕ, i < j → f i = f j → s ^ (j - i) ∈ U := by
      intro i j hlt hf
      apply hsub
      apply hEu
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' := congrArg (fun φ : E →ₐ[L] Ω => φ ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply] at hy'
      have hj : (s : G L Ω) ^ j = (s : G L Ω) ^ i * (s : G L Ω) ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hj] at hy'
      have hy'' : ((s : G L Ω) ^ i) y = ((s : G L Ω) ^ i) (((s : G L Ω) ^ (j - i)) y) := hy'
      have := ((s : G L Ω) ^ i).injective hy''
      show ((s ^ (j - i) : Ine (F := L) A) : G L Ω) • y = y
      rw [Subgroup.coe_pow]
      exact this.symm
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact ⟨j - i, Nat.sub_pos_of_lt hlt, key i j hlt hfij⟩
    · exact ⟨i - j, Nat.sub_pos_of_lt hlt, key j i hlt hfij.symm⟩
  have hrs : ∀ s : Ine (F := L) A,
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) = a.ρ (ineIncl h s) := by
    intro s
    obtain ⟨m, hm, hsm⟩ := hpow s
    have hrm : (r (s : G L Ω)) ^ m = 1 := by
      apply Units.ext
      have h1 := hU _ hsm
      rw [hN0, smul_zero, IsNilpotent.exp_zero] at h1
      rw [← map_pow, ← Subgroup.coe_pow, h1, Units.val_one]
    set f : Module.End ℂ (Fin n → ℂ) :=
      Matrix.toLin' ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) with hf
    have hfm : f ^ m = 1 := by
      rw [hf, ← htoEnd, ← map_pow, ← Units.val_pow_eq_pow_val, hrm, Units.val_one, map_one]
    have hfss : f.IsSemisimple := by
      apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := Polynomial.X ^ m - Polynomial.C 1)
      · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hm.ne') one_ne_zero).squarefree
      · simp [hfm]
    obtain ⟨hcomm, hnil⟩ := hFS (ineIncl h s)
    have hwd : toEndC ι (wdMat t hφ r N (ineIncl h s)) = f := by
      simp only [wdMat, hN0, smul_zero, IsNilpotent.exp_zero, mul_one]
      rfl
    simp only [hwd] at hcomm hnil
    have hss2 : (f - a.ρ (ineIncl h s)).IsSemisimple :=
      hfss.sub_of_commute hcomm.symm (a.semisimple _)
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss2)
  let P : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e : Module.End ℂ (Fin n → ℂ))
  let Pi : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (e.symm : Module.End ℂ (Fin n → ℂ))
  have hPPi : P * Pi = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e : Module.End ℂ (Fin n → ℂ)).comp (e.symm : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  have hPiP : Pi * P = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show (e.symm : Module.End ℂ (Fin n → ℂ)).comp (e : Module.End ℂ (Fin n → ℂ)) = LinearMap.id from
      LinearMap.ext fun v => by simp]
    exact LinearMap.toMatrix'_id
  let Φ := ι.symm.toRingHom.mapMatrix (m := Fin n)
  let g : GL (Fin n) (Qbar l) :=
    ⟨Φ P, Φ Pi, by rw [← map_mul, hPPi, map_one], by rw [← map_mul, hPiP, map_one]⟩
  refine ⟨g, fun s => ?_⟩
  have hA : a.ρ (ineIncl h s) = (e.symm : Module.End ℂ (Fin n → ℂ)).comp
      ((b.ρ (ineIncl h s)).comp (e : Module.End ℂ (Fin n → ℂ))) := by
    apply LinearMap.ext
    intro v
    simp [← he1]
  have hR : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι =
      Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P := by
    have h1 := congrArg LinearMap.toMatrix' (hrs s)
    rw [LinearMap.toMatrix'_toLin', hA, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hbρ s,
      LinearMap.toMatrix'_toLin', ← mul_assoc] at h1
    rw [h1]
    rfl
  have hback : (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Φ ((r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
    ext i j
    simp [Φ]
  show Φ P * (r (s : G L Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * Φ Pi = _
  rw [hback, hR, ← map_mul, ← map_mul]
  rw [show P * (Pi * Matrix.diagonal (fun i => ι (χ i s : Qbar l)) * P) * Pi =
      Matrix.diagonal (fun i => ι (χ i s : Qbar l)) by
    rw [← mul_assoc, ← mul_assoc, hPPi, one_mul, mul_assoc, hPPi, mul_one]]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Φ]
  · simp [Φ, Matrix.diagonal_apply_ne _ hij]
end
