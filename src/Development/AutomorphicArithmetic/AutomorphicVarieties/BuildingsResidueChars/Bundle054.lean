module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle029
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle069
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.isCrysAt_cyclotomic_zpow_restrict_decompositionGroup :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (j : ℤ), GlobalTheory.Pst.IsCrysAt (UpperTheory.V.Loc.PP l) Bw ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp ((cycBar F Ω l ^ j).comp (Dec (F := F) A).subtype)) := by
  intro F Ω _ _ _ _ _ l _ A O _ _ _ Bw j
  set P := UpperTheory.V.Loc.PP l with hP
  let θ : ↥(GK Bw.Kw) →* (↥Bw.LL.1)ˣ := cycLL (P.PD Bw.Kw) ↥Bw.LL.1 ^ j
  let r : ↥(Dec (F := F) A) →* GL (Fin 1) ↥Bw.LL.1 :=
    (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (θ.comp Bw.e.toMonoidHom)
  have hr : ∀ g, ((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) =
      ((θ (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) • (1 : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) := fun g =>
    GlobalTheory.HodgeOfTrue.coe_scalar _
  have key : ∀ g : ↥(Dec (F := F) A), algebraMap ↥Bw.LL.1 (Om l)
      ((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g) : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      ((cycBar F Ω l (g : G F Ω) : (Qbar l)ˣ) : Qbar l) := fun g => by
    have h1 := GlobalTheory.BlockCrys.cyc_bridge Bw P (Bw.e g)
    have h2 := P.PD_χ Bw.Kw (Bw.e g)
    have h3 : Br.ι Bw (Bw.e g) = g := Bw.e.symm_apply_apply g
    rw [h3] at h1
    change algebraMap ↥Bw.LL.1 (Om l) (algebraMap ℚ_[l] ↥Bw.LL.1 (((P.PD Bw.Kw).χ (Bw.e g) : ℚ_[l]ˣ) : ℚ_[l])) = _
    rw [h2, h1, ← IsScalarTower.algebraMap_apply]
    rfl
  refine ⟨Bw.LL, r, ⟨le_rfl, ?_⟩, ?_⟩
  · ext g a b
    change algebraMap ↥Bw.LL.1 (Om l) (((r g : GL (Fin 1) ↥Bw.LL.1) : Matrix (Fin 1) (Fin 1) ↥Bw.LL.1) a b) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 1) ((cycBar F Ω l ^ j) (g : G F Ω)) : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) a b
    rw [hr, GlobalTheory.HodgeOfTrue.coe_scalar, Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change algebraMap ↥Bw.LL.1 (Om l) (((cycLL (P.PD Bw.Kw) ↥Bw.LL.1 (Bw.e g)) ^ j : (↥Bw.LL.1)ˣ) : ↥Bw.LL.1) =
      (((cycBar F Ω l (g : G F Ω)) ^ j : (Qbar l)ˣ) : Qbar l)
    rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, key]
  · haveI := Bw.LL.2
    have h1 := GlobalTheory.BlockCrys.isCrys_cyc_zpow (LL := ↥Bw.LL.1) (P.PD Bw.Kw) j
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥Bw.LL.1 ↥Bw.LL.1).symm
      (fun g x => ?_) h1
    rw [GlobalTheory.ConjLocal.repE_apply, hr, MulEquiv.apply_symm_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    funext a
    rfl
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU GlobalTheory.Branching
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem irr_emb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation.IsIrreducible ((sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  have heq : (sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (smallRep (unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change sqRep ℂ n lam (cEmb τ (x : UA E n)) = sqRep ℂ n lam (unitaryIncl n (e x))
    rw [he]
  rw [heq]
  exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv (isIrreducible_smallRep_unitary n lam)

private noncomputable def locRep (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation ℂ ((embU n τ).subgroupOf (infU E n)) (nablaSq ℂ n lam) :=
  (sqRep ℂ n lam).comp ((cEmb τ).comp ((infU E n).subtype.comp (Subgroup.subtype _)))

private theorem irr_locRep (τ : E →+* ℂ) (lam : DomWeight n) : (locRep τ lam).IsIrreducible :=
  GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ (Subgroup.subgroupOfEquivOfLe (embU_le_infU τ)) (irr_emb τ lam)

private noncomputable def repN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) : Representation ℂ (infU E n) N where
  toFun x :=
    { toFun := fun F => ⟨fun k => RU E n x (F.1 k), hN x x.2 F.1 F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext F k g
    simp
  map_mul' x y := by
    ext F k : 3
    exact (RU_RU x.1 y.1 (F.1 k)).symm

private theorem isoN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) (σ : Submodule ℂ (UA E n → ℂ))
    (hσ : IsAutRepU σ) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ) (τ : E →+* ℂ) (lam : DomWeight n) (h : HasWeightAt σ τ lam) :
    (⨆ f : {f : nablaSq ℂ n lam →ₗ[ℂ] N // ∀ (g : (embU n τ).subgroupOf (infU E n)) v,
      f (locRep τ lam g v) = repN N hN g (f v)}, LinearMap.range f.1) = ⊤ := by
  let π : AutSub E n := ⟨σ, hσ⟩
  have h1 := iSup_range_weight_eq_top E n π τ lam h
  refine UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ π.V (locRep τ lam) (π.rep.comp ((infU E n).subtype.comp (Subgroup.subtype _)))
    (irr_locRep τ lam) ?_ N ((repN N hN).comp (Subgroup.subtype _)) (Fin m)
    (fun k => ((LinearMap.proj k).comp N.subtype).codRestrict σ fun F => hNσ F.1 F.2 k) (fun _ _ _ => rfl)
    (fun y hy => Subtype.ext (funext fun k => congrArg Subtype.val (hy k)))
  refine top_le_iff.1 (h1.ge.trans (iSup_le fun f => ?_))
  exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' ⟨g.1.1, g.2⟩) v⟩ le_rfl

private theorem exists_multi {I : Type} [Finite I] (emb : I → (E →+* ℂ))
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) (lam : I → DomWeight n)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hw : ∀ i, HasWeightAt σ (emb i) (lam i)) {m : ℕ}
    (N : Submodule ℂ (Fin m → UA E n → ℂ)) (h0 : N ≠ ⊥) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ)
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) :
    ∃ μ : MultilinearMap (RingHom.id ℂ) (fun i => nablaSq ℂ n (lam i)) N, μ ≠ 0 ∧ ∀ x ∈ infU E n, ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k := by
  classical
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨hgen, hcomm⟩ := UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute E n
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups (infU E n) I (fun i => (embU n (emb i)).subgroupOf (infU E n))
    (fun i j hij a ha b hb' => Subtype.ext (hcomm (emb i) (emb j) (fun e => hij (hb.1 e)) a.1 ha b.1 hb'))
    (fun i => nablaSq ℂ n (lam i)) (fun i => locRep (emb i) (lam i)) (fun i => irr_locRep _ _) N (repN N hN)
    (fun i => isoN N hN σ hσ hNσ (emb i) (lam i) (hw i))
  refine ⟨μ, hμ0, fun x hx => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k) (hgen hx) ?_ ?_ ?_
  · intro τ y hy v k
    obtain ⟨i, hi⟩ := hb.2 (InfinitePlace.mk τ)
    have hi' : InfinitePlace.mk (emb i) = InfinitePlace.mk τ := hi
    have hy' : y ∈ embU n (emb i) := by
      unfold embU at hy ⊢
      rwa [hi']
    have h2 := hμ i ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ v
    have h3 : (fun j => sqRep ℂ n (lam j) (cEmb (emb j) y) (v j)) =
        Function.update v i (locRep (emb i) (lam i) ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ (v i)) := by
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        rfl
      · have h4 := (Subgroup.mem_inf.1 hy').2
        rw [Subgroup.mem_iInf] at h4
        have h5 := h4 (emb j)
        rw [Subgroup.mem_iInf] at h5
        have h6 : cEmb (emb j) y = 1 := h5 fun e' => e (hb.1 e')
        rw [Function.update_of_ne e, h6, map_one, Module.End.one_apply]
    rw [h3, h2]
    rfl
  · intro v k
    simp only [map_one, Module.End.one_apply]
  · intro a b ha hb v k
    rw [← RU_RU, hb, ha]
    simp only [map_mul, Module.End.mul_apply]

end

private theorem dualDistrib_comp_map {I : Type} [Finite I] {M : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (f : ∀ i, Module.Dual ℂ (M i)) (g : ∀ i, M i →ₗ[ℂ] M i) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) ∘ₗ PiTensorProduct.map g =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun i => f i ∘ₗ g i) := by
  have := Fintype.ofFinite I
  ext v
  simp [PiTensorProduct.dualDistrib_apply]

theorem UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (emb : I → (E →+* ℂ)), Function.Bijective (fun i => InfinitePlace.mk (emb i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → (∀ i, HasWeightAt σ (emb i) (lam i).dual) → ∀ (m : ℕ) (N : Submodule ℂ (Fin m → UA E n → ℂ)), N ≠ ⊥ → (∀ F ∈ N, ∀ k, F k ∈ σ) → (∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) → ∃ Φ : Module.Dual ℂ (⨂[ℂ] i : I, nablaSq ℂ n (lam i)) →ₗ[ℂ] (Fin m → UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧ ∀ ℓ, ∀ x ∈ infU E n, ∀ k, RU E n x (Φ ℓ k) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) x⁻¹)) k := by
  intro E _ _ _ n hn I _ emb hb lam σ hσ hw m N h0 hNσ hN
  obtain ⟨μ, hμ0, hμ⟩ := exists_multi emb hb (fun i => (lam i).dual) σ hσ hw N h0 hNσ hN
  choose κ hκ using fun i => UpperTheory.exists_dual_schur_module_iso_dual_weight n hn (lam i)
  let D := PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => nablaSq ℂ n (lam i))
  have hD : ∀ t, D t = PiTensorProduct.dualDistrib t := fun _ => rfl
  let Ψ := PiTensorProduct.lift (μ.compLinearMap fun i => (κ i).toLinearMap)
  have hΦ : ∀ f, (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) (D (PiTensorProduct.tprod ℂ f)) =
      (μ fun i => κ i (f i)).1 := by
    intro f
    change (Ψ (D.symm (D _))).1 = _
    rw [D.symm_apply_apply, PiTensorProduct.lift.tprod]
    rfl
  refine ⟨N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap, fun h => hμ0 ?_, fun ℓ => (Ψ (D.symm ℓ)).2, fun ℓ x hx k => ?_⟩
  · ext v : 1
    have := hΦ fun i => (κ i).symm (v i)
    rw [h] at this
    simp only [LinearEquiv.apply_symm_apply] at this
    exact Subtype.ext this.symm
  · obtain ⟨t, rfl⟩ := D.surjective ℓ
    generalize (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) = Φ at hΦ
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, LinearMap.smul_comp, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, map_smul]
      congr 1
      rw [hΦ, hμ x hx, hD, dualDistrib_comp_map, ← hD, hΦ]
      simp only [map_inv (cEmb _), hκ]
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_comp, Pi.add_apply, ha, hb]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 E), normV v = Ideal.absNorm v.asIdeal := by
    intro v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [cPl_asIdeal]
  exact (Ideal.map_symm _).symm

private theorem conj_algebraMap {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E]
    [Algebra F E] (x : F) : IsCMField.complexConj E (algebraMap F E x) = algebraMap F E x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))
  exact RingHom.congr_fun h x

theorem UpperTheory.baseChange_complexConj_invariance :
    UpperTheory.V.Af.Bc.BcConj := by
  intro F E _ _ _ _ _ _ _ n π P h
  have h1 := h.unr
  have h2 := (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually h1
  filter_upwards [h1, h2] with w a b
  obtain ⟨B, hB, hP⟩ := a (w.under (𝓞 F)) rfl _ (normV_under w)
  obtain ⟨B', hB', hP'⟩ := b (w.under (𝓞 F)) (by
    have e := cPl_asIdeal w
    change _ = (cPl w).asIdeal.comap _
    rw [e]
    ext x
    have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv (algebraMap (𝓞 F) (𝓞 E) x) =
        algebraMap (𝓞 F) (𝓞 E) x := RingOfIntegers.ext (conj_algebraMap (x : F))
    rw [Ideal.mem_comap, Ideal.mem_comap, e2]
    rfl) _ ((normV_cPl w).trans (normV_under w))
  obtain rfl := TR.CuspSub.HasSat.unique hB hB'
  exact ⟨_, hP, hP'⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    ∃ (d : 𝓞 F) (t : E), d ≠ 0 ∧ t * t = algebraMap F E d ∧ (∀ c : F, algebraMap F E c ≠ t) ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * t := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h⟩
  obtain ⟨δ, e, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F E
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) δ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
  have hb2 : algebraMap F E (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hδ (by simp)
  refine ⟨a * b, algebraMap F E (algebraMap (𝓞 F) F b) * e 1, mul_ne_zero ha0 hb0, ?_, fun c hc => ?_, fun x => ?_⟩
  · rw [mul_mul_mul_comm, h1, ← map_mul, ← map_mul]
    congr 1
    show _ = algebraMap (𝓞 F) F (a * b)
    rw [map_mul]
    field_simp
  · apply hδ
    refine ⟨c / algebraMap (𝓞 F) F b, (algebraMap F E).injective ?_⟩
    rw [← h1, map_mul, map_div₀, hc]
    field_simp
  · refine ⟨e.repr x 0, e.repr x 1 / algebraMap (𝓞 F) F b, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, map_div₀, Algebra.smul_def, Algebra.smul_def]
    field_simp

theorem UpperTheory.exists_quadratic_sign_character :
    UpperTheory.V.Af.Bc.SignEx := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ h
  classical
  obtain ⟨d, t, hd, ht, hn, hx⟩ := exists_gen F E h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F E Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  set θ : Ω := algebraMap E Ω t with hθ
  have hθ2 : θ * θ = algebraMap F Ω d := by
    rw [hθ, ← map_mul, ht, ← IsScalarTower.algebraMap_apply]
  have hd' : algebraMap F Ω d ≠ 0 := by simpa using hd
  have hθ0 : θ ≠ 0 := fun h0 => hd' (by rw [← hθ2, h0, zero_mul])
  have hne : -θ ≠ θ := fun h0 => hθ0 (by linear_combination (-1 / 2 : Ω) * h0)
  have hpm : ∀ s : _root_.Formalism.ConjugateSelfDual.G F Ω, s θ = θ ∨ s θ = -θ := fun s => by
    apply mul_self_eq_mul_self_iff.1
    rw [← map_mul, hθ2, AlgEquiv.commutes]
  have hm1 : (-1 : (Qbar l)ˣ) ≠ 1 := fun h0 => by
    have := congrArg Units.val h0
    simp only [Units.val_neg, Units.val_one] at this
    exact absurd this (by norm_num)
  let δ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ := MonoidHom.mk' (fun s => if s θ = θ then 1 else -1) fun a b => by
    rcases hpm a with ha | ha <;> rcases hpm b with hb | hb <;>
      simp [AlgEquiv.mul_apply, ha, hb, hne]
  have hδ : ∀ s, δ s = 1 ↔ s θ = θ := fun s => by
    show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ↔ _
    split_ifs with h0 <;> simp [h0, hm1]
  refine ⟨δ, continuous_of_isOpen_ker' δ ?_, fun h1 => ?_, ⟨fun s => ?_, fun s => ?_⟩, ?_⟩
  · have e : δ.ker = MulAction.stabilizer (_root_.Formalism.ConjugateSelfDual.G F Ω) θ := Subgroup.ext fun s => hδ s
    rw [e]
    exact stabilizer_isOpen_of_isIntegral θ
  · have hfix : θ ∈ (⊥ : IntermediateField F Ω) := by
      rw [← InfiniteGalois.fixedField_bot]
      intro s
      exact (hδ s.1).1 (by rw [h1]; rfl)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
    refine hn c ((algebraMap E Ω).injective ?_)
    rw [← IsScalarTower.algebraMap_apply, hc]
  · rw [hδ]
    constructor
    · intro hs
      refine ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => ?_, rfl⟩
      obtain ⟨a, b, rfl⟩ := hx x
      show s _ = _
      rw [map_add (f := _), map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_add (f := _), map_mul,
        AlgEquiv.commutes, AlgEquiv.commutes, ← hθ, hs]
    · rintro ⟨u, rfl⟩
      exact u.commutes t
  · show (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = 1 ∨ (if s θ = θ then (1 : (Qbar l)ˣ) else -1) = -1
    split_ifs <;> simp
  · have h4 : Ideal.span {(4 * d : 𝓞 F)} ≠ 0 := by simpa using hd
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h4).subset fun v hv => ?_)
    by_contra hv'
    apply hv
    intro A hA s hs
    rw [hδ]
    refine (hpm s).resolve_right fun h0 => hv' ?_
    have hle : A.valuation θ ≤ 1 := by
      have h1 : A.valuation (θ * θ) ≤ 1 := by
        rw [hθ2]
        exact int_le A (map_isIntegral_int (algebraMap F Ω) d.isIntegral_coe)
      rw [map_mul] at h1
      by_contra h2
      exact absurd h1 (not_le.2 (one_lt_mul'' (not_le.1 h2) (not_le.1 h2)))
    have hlt := hs.2 θ hle
    rw [h0] at hlt
    show v.asIdeal ∣ _
    rw [Ideal.dvd_span_singleton, ← hA]
    have e : algebraMap F Ω ((4 * d : 𝓞 F) : F) = (-θ - θ) * (-θ - θ) := by
      have : ((4 * d : 𝓞 F) : F) = 4 * (d : F) := by
        show algebraMap (𝓞 F) F (4 * d) = _
        rw [map_mul, map_ofNat]
      rw [this, map_mul, ← hθ2, map_ofNat]
      ring
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hlt.le
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.ideleNorm_valuation_of_local_compatibility :
    UpperTheory.V.Af.Bc.NormLoc → UpperTheory.V.Af.Bc.NormVal := by
  intro hN
  unfold UpperTheory.V.Af.Bc.NormLoc at hN
  unfold UpperTheory.V.Af.Bc.NormVal
  intro E _ _ _ χ w f hf hχ
  set u := HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w with hu
  have hunr : ∀ x : (HeightOneSpectrum.adicCompletion _ u)ˣ, IsUnitAt u x → χ.loc u x = 1 := by
    unfold HChar.UnrAt at hχ
    exact hχ
  have hloc : ∀ x : (HeightOneSpectrum.adicCompletion E w)ˣ,
      ((compNorm E) χ).loc w x = (χ : Ideles _ →* ℂˣ) (ideleNorm E (localIdele E w x)) := fun x => rfl
  have hlocF : ∀ y : (HeightOneSpectrum.adicCompletion _ u)ˣ,
      χ.loc u y = (χ : Ideles _ →* ℂˣ) (localIdele _ u y) := fun y => rfl
  constructor
  · unfold HChar.UnrAt
    intro x hx
    obtain ⟨y, hy, hv⟩ := hN E w x
    rw [hloc, hy, ← hlocF]
    apply hunr
    unfold IsUnitAt at hx ⊢
    rw [hv f hf, hx, one_pow]
  · have hvw : ((compNorm E) χ).val w = ((compNorm E) χ).loc w (atFin w (unif w)) := rfl
    have hvu : χ.val u = χ.loc u (atFin u (unif u)) := rfl
    have hpw : IsUnifAt w (atFin w (unif w)) := Classical.choose_spec (exists_unif w)
    have hpu : IsUnifAt u (atFin u (unif u)) := Classical.choose_spec (exists_unif u)
    unfold IsUnifAt at hpw hpu
    obtain ⟨y, hy, hv⟩ := hN E w (atFin w (unif w))
    rw [hvw, hvu, hloc, hy, ← hlocF, ← map_pow]
    have hone : χ.loc u (y * ((atFin u (unif u)) ^ f)⁻¹) = 1 := by
      apply hunr
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
        hv f hf, hpw, hpu, mul_inv_cancel₀]
      exact pow_ne_zero _ (by simp)
    rw [map_mul, map_inv, mul_inv_eq_one] at hone
    exact hone
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.schur_twist_holds :
    UpperTheory.V.Af.Bc.SchurTw :=
  _root_.UpperTheory.Reformulated.B.H13.schur_twist_holds
end
