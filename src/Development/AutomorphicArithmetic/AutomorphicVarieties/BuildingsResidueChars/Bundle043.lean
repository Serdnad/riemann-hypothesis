module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle157
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Artinian.Instances
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.V.hasFixed_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (e : ρ.Equiv τ) {U : Subgroup G}
    (h : UpperTheory.V.Af.HasFixed τ U) : UpperTheory.V.Af.HasFixed ρ U := by
  obtain ⟨v, hv, hU⟩ := h
  refine ⟨e.symm.toLinearEquiv v, by simpa using hv, fun u hu => ?_⟩
  have h1 := LinearMap.congr_fun (e.symm.isIntertwining' u) v
  simp only [LinearMap.comp_apply, hU u hu] at h1
  exact h1.symm

private theorem UpperTheory.V.hasFixed_of_nu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (s : ℂ) (U : Subgroup (GL (Fin x.1) k))
    (hU : U ≤ GlobalTheory.SplitWeil.KO k (Fin x.1)) (h : UpperTheory.V.Af.HasFixed (x.nu s).rep U) :
    UpperTheory.V.Af.HasFixed x.rep U := by
  obtain ⟨v, hv, h1⟩ := UpperTheory.V.hasFixed_of_equiv (x.twEquiv _ _) h
  refine ⟨v, hv, fun u hu => ?_⟩
  have h2 := h1 u hu
  rwa [GlobalTheory.SmGL.twist_apply, detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) (hU hu), Units.val_one,
    one_smul] at h2

theorem UpperTheory.hasFixed_of_algNorm_fixed_ne_bot :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (w.adicCompletion F))), U ≤ GlobalTheory.SplitWeil.KO (w.adicCompletion F) (Fin n) →
    GlobalTheory.PRep.fixed (algNorm σ).rep U ≠ ⊥ → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ w n σ U hU h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine UpperTheory.V.hasFixed_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) ?_
  refine UpperTheory.V.hasFixed_of_nu (IrrGL.of σ.ρ σ.smooth σ.irred) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) U hU ⟨v, hv0, ?_⟩
  exact fun u hu => (hv ⟨u, hu⟩).trans (by simp)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

private theorem detPow_invTr (n : ℕ) (g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (inside₂ ℂ n g) c = detPow ℂ n g⁻¹ c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

private theorem toDual_invTr (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) ℂ) (x : nablaSq ℂ n lam) :
    GlobalTheory.ConjDual.toDual n lam (GlobalTheory.Branching.sqRep ℂ n lam (inside₂ ℂ n g) x) =
      GlobalTheory.ConjDual.toDual n lam x ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹ := by
  ext y
  change GlobalTheory.ConjDual.bil _ (sqAct ℂ n lam (inside₂ ℂ n g) x.1) y.1 =
    GlobalTheory.ConjDual.bil _ x.1 (sqAct ℂ n lam g⁻¹ y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_invTr, GlobalTheory.ConjDual.bil_rowAct,
    Matrix.transpose_transpose]
  rfl

theorem UpperTheory.exists_dual_schur_module_iso_dual_weight :
    ∀ (n : ℕ), 1 ≤ n → ∀ lam : DomWeight n, ∃ κ : Module.Dual ℂ (nablaSq ℂ n lam) ≃ₗ[ℂ] nablaSq ℂ n lam.dual, ∀ (g : GL (Fin n) ℂ) (ℓ : Module.Dual ℂ (nablaSq ℂ n lam)), κ (ℓ ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹) = GlobalTheory.Branching.sqRep ℂ n lam.dual g (κ ℓ) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.DefiniteBC.exists_equiv_dual lam
  let T : nablaSq ℂ (m + 1) lam ≃ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ (m + 1) lam) :=
    (GlobalTheory.ConjDual.toDual (m + 1) lam).linearEquivOfInjective (GlobalTheory.ConjDual.toDual_injective _ lam)
      Subspace.dual_finrank_eq.symm
  have hT : ∀ x, T x = GlobalTheory.ConjDual.toDual (m + 1) lam x := fun _ => rfl
  refine ⟨T.symm.trans κ, fun g ℓ => ?_⟩
  obtain ⟨x, rfl⟩ := T.surjective ℓ
  rw [hT x, ← toDual_invTr, ← hT, ← hT, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    T.symm_apply_apply, T.symm_apply_apply, hκ, GlobalTheory.DefiniteBC.invTr_invTr]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private def gl2ToGL3BlockMatrix {k : Type} [Field k] (a : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) k :=
  !![a 0 0, 0, a 0 1; 0, 1, 0; a 1 0, 0, a 1 1]

private theorem gl2ToGL3BlockMatrix_mul {k : Type} [Field k] (a b : Matrix (Fin 2) (Fin 2) k) :
    gl2ToGL3BlockMatrix (a * b) = gl2ToGL3BlockMatrix a * gl2ToGL3BlockMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2ToGL3BlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_embedding_one {k : Type} [Field k] :
    gl2ToGL3BlockMatrix (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2ToGL3BlockMatrix]

private def gl2ToGL3BlockHom {k : Type} [Field k] : GL (Fin 2) k →* GL (Fin 3) k :=
  Units.map ({ toFun := gl2ToGL3BlockMatrix, map_one' := block_embedding_one, map_mul' := gl2ToGL3BlockMatrix_mul } :
    Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 3) (Fin 3) k)

theorem UpperTheory.block_conjugate_rank_three_rep :
    ∀ (Γ Δ k : Type) [Group Γ] [Group Δ] [Field k] (φ : Γ → Δ) (W W' : Δ →* GL (Fin 2) k) (ρ ρ' : Γ →* GL (Fin 3) k) (g g' : GL (Fin 3) k), (∀ s, ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W (φ s) 0 0, 0, W (φ s) 0 1; 0, 1, 0; W (φ s) 1 0, 0, W (φ s) 1 1]) → (∀ s, ((g' * ρ' s * g'⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W' (φ s) 0 0, 0, W' (φ s) 0 1; 0, 1, 0; W' (φ s) 1 0, 0, W' (φ s) 1 1]) → RepIso W W' → RepIso ρ ρ' := by
  intro Γ Δ k _ _ _ φ W W' ρ ρ' g g' hρ hρ' hWW
  obtain ⟨h, hh⟩ := hWW
  let H : GL (Fin 3) k := gl2ToGL3BlockHom h
  have c : ∀ s, g' * ρ' s * g'⁻¹ = H * (g * ρ s * g⁻¹) * H⁻¹ := by
    intro s
    apply Units.ext
    have e1 : ((H * (g * ρ s * g⁻¹) * H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (H : Matrix (Fin 3) (Fin 3) k) * ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          ((H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [Units.val_mul, Units.val_mul]
    rw [e1, hρ s, hρ' s]
    change gl2ToGL3BlockMatrix ((W' (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      gl2ToGL3BlockMatrix (h : Matrix (Fin 2) (Fin 2) k) * gl2ToGL3BlockMatrix ((W (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        gl2ToGL3BlockMatrix ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [hh (φ s), Units.val_mul, Units.val_mul, gl2ToGL3BlockMatrix_mul, gl2ToGL3BlockMatrix_mul]
  refine ⟨g'⁻¹ * H * g, fun s => ?_⟩
  calc ρ' s = g'⁻¹ * (g' * ρ' s * g'⁻¹) * g' := by group
    _ = g'⁻¹ * (H * (g * ρ s * g⁻¹) * H⁻¹) * g' := by rw [c s]
    _ = g'⁻¹ * H * g * ρ s * (g'⁻¹ * H * g)⁻¹ := by group
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.isIrr_twist_and_repIso_of_twist_repIso :
    ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (χ : Γ →* kˣ), (∀ r : Γ →* GL (Fin n) k, IsIrr r → IsIrr (tw r χ)) ∧ ∀ r r' : Γ →* GL (Fin n) k, RepIso (tw r χ) (tw r' χ) → RepIso r r' := by
  intro Γ k _ _ n χ
  have key : ∀ (r : Γ →* GL (Fin n) k) W, IsInv (tw r χ) W ↔ IsInv r W := fun r W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  refine ⟨fun r hr => ?_, fun r r' ⟨g, hg⟩ => ⟨g, fun s => ?_⟩⟩
  · unfold IsIrr IsIrrSub at hr ⊢
    simpa only [key] using hr
  · have h := congrArg Units.val (hg s)
    apply Units.ext
    simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul] at h ⊢
    exact smul_right_injective _ (Units.ne_zero (χ s)) h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open Formalism.MainNotions.N (IsSSRep IsInv)
open scoped Matrix

private noncomputable def diagRep {G : Type} [Group G] {n : ℕ} (χ : Fin n → G →* ℂˣ) : G →* GL (Fin n) ℂ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) ℂ).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => ℂ)).symm.toMonoidHom.comp (MonoidHom.pi χ))

private theorem commute_of_semisimple_of_charpoly_prod_chars {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (χ : Fin n → G →* ℂˣ) (hss : ∀ g, (T g).IsSemisimple)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ))) (g k : G) :
    Commute (T g) (T k) := by
  have hone : T (g * k * g⁻¹ * k⁻¹) = 1 := by
    have h1 : (T (g * k * g⁻¹ * k⁻¹)).charpoly = (X - C (1 : ℂ)) ^ n := by
      rw [hcp]
      have : ∀ i, ((χ i (g * k * g⁻¹ * k⁻¹) : ℂˣ) : ℂ) = 1 := by
        intro i
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      simp [this]
    have hdvd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ (X - C (1 : ℂ)) ^ n :=
      h1 ▸ LinearMap.minpoly_dvd_charpoly _
    have hd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ X - C (1 : ℂ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact dvd_trans (by simpa using hdvd) (one_dvd _)
      · exact ((hss _).minpoly_squarefree.dvd_pow_iff_dvd hn.ne').mp hdvd
    have := (minpoly.dvd_iff).mp hd
    simpa [sub_eq_zero] using this
  have hgk : g * k = (g * k * g⁻¹ * k⁻¹) * (k * g) := by group
  have h2 : T (g * k) = T (g * k * g⁻¹ * k⁻¹) * T (k * g) := by
    rw [← map_mul, ← hgk]
  rw [hone, one_mul, map_mul, map_mul] at h2
  exact h2

private theorem exists_basis_eigen_of_semisimple_commuting {G : Type} [Group G] {m : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (hss : ∀ g, (T g).IsSemisimple) (hc : ∀ g k, Commute (T g) (T k)) :
    ∃ (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ), ∀ j g, T g (b j) = c j g • b j := by
  classical
  let A : (G → ℂ) → Submodule ℂ (Fin m → ℂ) := fun φ => ⨅ g, (T g).maxGenEigenspace (φ g)
  have hmaps : ∀ (g k : G) (μ : ℂ), Set.MapsTo (T g) ((T k).maxGenEigenspace μ) ((T k).maxGenEigenspace μ) :=
    fun g k μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc k g) μ
  have hind : iSupIndep A :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun g => T g) hmaps
  have htop : iSup A = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun g => T g) hmaps
      (fun g => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hint : DirectSum.IsInternal A := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v : (φ : G → ℂ) → Module.Basis (Module.Free.ChooseBasisIndex ℂ (A φ)) ℂ (A φ) :=
    fun φ => Module.Free.chooseBasis ℂ (A φ)
  let b0 := hint.collectedBasis v
  let e := b0.indexEquiv (Pi.basisFun ℂ (Fin m))
  refine ⟨b0.reindex e, fun j => (e.symm j).1, fun j g => ?_⟩
  have hmem : b0 (e.symm j) ∈ A (e.symm j).1 := hint.collectedBasis_mem v _
  have hmem' : b0 (e.symm j) ∈ (T g).eigenspace ((e.symm j).1 g) := by
    have := (Submodule.mem_iInf _).mp hmem g
    rwa [(hss g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp hmem'

private theorem exists_linearEquiv_diagonal_chars_of_eigenbasis {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ)) (χ : Fin n → G →* ℂˣ)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)))
    (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ) (hT : ∀ j g, T g (b j) = c j g • b j) :
    ∃ e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ),
      ∀ g v, e (T g v) = Matrix.toLin' (Matrix.diagonal fun i => ((χ i g : ℂˣ) : ℂ)) (e v) := by
  classical
  have hinj : ∀ j, Function.Injective fun z : ℂ => z • b j := fun j => smul_left_injective ℂ (b.ne_zero j)
  have hone : ∀ j, c j 1 = 1 := by
    intro j
    apply hinj j
    simp only
    rw [← hT, map_one, one_smul]
    rfl
  have hmul : ∀ j g k, c j (g * k) = c j g * c j k := by
    intro j g k
    apply hinj j
    simp only
    rw [← hT, map_mul, Module.End.mul_apply, hT, map_smul, hT, smul_smul, mul_comm]
  let ψ : Fin m → (G →* ℂ) := fun j => ⟨⟨c j, hone j⟩, hmul j⟩
  let χ' : Fin n → (G →* ℂ) := fun i => (Units.coeHom ℂ).comp (χ i)
  have hroots : ∀ {k : ℕ} (d : Fin k → ℂ), (∏ j, (X - C (d j))).roots = Finset.univ.val.map d := by
    intro k d
    rw [Finset.prod_eq_multiset_prod,
      show Finset.univ.val.map (fun j => X - C (d j)) = (Finset.univ.val.map d).map (fun a => X - C a) by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hdiag : ∀ g, LinearMap.toMatrix b b (T g) = Matrix.diagonal fun j => c j g := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply, hT, map_smul, b.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hsum : ∀ g, ∑ j, c j g = ∑ i, ((χ i g : ℂˣ) : ℂ) := by
    intro g
    have hp := LinearMap.charpoly_toMatrix (T g) b
    rw [hdiag, Matrix.charpoly_diagonal, hcp] at hp
    have := congrArg (fun p => p.roots.sum) hp
    simpa [hroots, Finset.sum_eq_multiset_sum] using this
  have hcount : ∀ φ : G →* ℂ,
      Fintype.card {j // ψ j = φ} = Fintype.card {i // χ' i = φ} := by
    intro φ
    have hli := linearIndependent_monoidHom G ℂ
    set l : (G →* ℂ) →₀ ℂ := ∑ j, Finsupp.single (ψ j) 1 - ∑ i, Finsupp.single (χ' i) 1 with hl
    have hlc : Finsupp.linearCombination ℂ (fun f : G →* ℂ => (f : G → ℂ)) l = 0 := by

      rw [hl, map_sub, map_sum, map_sum]
      simp only [Finsupp.linearCombination_single, one_smul]
      funext g
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
      have := hsum g
      simp only [ψ, χ', MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply]
      rw [this, sub_self]
    have hl0 : l = 0 := linearIndependent_iff.mp hli l hlc
    have hφ := congrArg (fun f => f φ) hl0
    simp only [hl, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finset.sum_boole, sub_eq_zero] at hφ
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact_mod_cast hφ
  let π : Fin m ≃ Fin n := Equiv.ofFiberEquiv (f := ψ) (g := χ') fun φ => Fintype.equivOfCardEq (hcount φ)
  have hπ : ∀ j, χ' (π j) = ψ j := fun j => Equiv.ofFiberEquiv_map _ j
  have hcoord : ∀ g v k, b.repr (T g v) k = c k g * b.repr v k := by
    intro g v k
    have := b.ext (f₁ := (Finsupp.lapply k).comp (b.repr.toLinearMap.comp (T g)))
      (f₂ := c k g • (Finsupp.lapply k).comp b.repr.toLinearMap) (by
        intro j
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, map_smul, b.repr_self,
          Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases h : j = k
        · subst h; simp
        · simp [h])
    simpa using LinearMap.congr_fun this v
  refine ⟨b.equivFun.trans (LinearEquiv.funCongrLeft ℂ ℂ π.symm), fun g v => ?_⟩
  ext i
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.equivFun_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal, hcoord]
  congr 1
  have h1 := hπ (π.symm i)
  rw [Equiv.apply_symm_apply] at h1
  have h2 := congrArg (fun f : G →* ℂ => f g) h1
  simpa [ψ, χ'] using h2.symm

theorem UpperTheory.isTypeWeilDeligne_iff_monodromy_zero_charpoly :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → Ine (F := L) A →* ℂˣ) (x : WD h), IsTypeWD h χ x ↔ x.mono0 ∧ ∀ s, x.charPol (ineIncl h s) = ∏ i, (X - C (χ i s : ℂ)) := by
  intro L Ω _ _ _ _ _ n w A h χ x
  constructor
  · rintro ⟨b, rfl, hN, hb⟩
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).mpr hN, fun s => ?_⟩
    rw [WD.charPol_mk, hb, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
  · rintro ⟨h0, hc⟩
    obtain ⟨m, a, rfl⟩ := WD.exists_rep x
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
    let T : ↥(Ine (F := L) A) →* Module.End ℂ (Fin m → ℂ) := a.ρ.comp (ineIncl h)
    have hss : ∀ g, (T g).IsSemisimple := fun g => a.semisimple _
    have hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)) := by
      intro g
      have := hc g
      rwa [WD.charPol_mk] at this
    obtain ⟨bs, c, hT⟩ := exists_basis_eigen_of_semisimple_commuting T hss (commute_of_semisimple_of_charpoly_prod_chars T χ hss hcp)
    obtain ⟨e, he⟩ := exists_linearEquiv_diagonal_chars_of_eigenbasis T χ hcp bs c hT
    refine ⟨a.transport e, ?_, ?_, ?_⟩
    · refine (WD.sound ⟨e, fun σ v => ?_, fun v => ?_⟩).symm
      · simp [WDRep.transport]
      · simp [WDRep.transport]
    · simp [WDRep.transport, h0]
    · intro s
      apply LinearMap.ext
      intro u
      have := he s (e.symm u)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      simp [WDRep.transport, T]
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_tri {R : Type} [CommRing R] {A : M4 R} (h : IsUp A) : (adj A).BlockTriangular id := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem adj_dg {R : Type} [CommRing R] (A : M4 R) (i : Fin 4) : adj A i i = A i.rev i.rev := by
  rw [adj_apply]
  fin_cases i <;> simp [sgn]

theorem UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair a P → ∀ (v : Φ.ι) (i : Fin 4), P.ψ v i 1 = 1 ∧ (∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t) ∧ ∀ s ∈ Φ.Gv v, P.ψ v i s * P.ψ v i.rev s = a (Φ.ν s) := by
  intro O Γ _ _ Φ R _ a P hP v i
  have hn : adj (P.n v) * P.n v = 1 := by
    have h := (hP.low v).1
    unfold IsGSp at h
    simpa using h
  have hn' : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.mp hn
  refine ⟨?_, ?_, ?_⟩
  · simp [PD.ψ, hn]
  · intro s hs t ht
    have e : adj (P.n v) * P.r (s * t) * P.n v =
        (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r t * P.n v) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul]
    unfold PD.ψ
    rw [e]
    exact UpperTheory.V.Loc.SpFlag.tri_mul_diag (fun p q h => hP.flag v s hs p q h) (fun p q h => hP.flag v t ht p q h) i
  · intro s hs
    have hB := hP.flag v s hs
    have hg := hP.mult s
    unfold IsGSp at hg
    have e : adj (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r s * P.n v) = a (Φ.ν s) • 1 := by
      rw [UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_adj]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul, ← Matrix.mul_assoc (adj (P.r s)), hg]
      simp [hn]
    have d := UpperTheory.V.Loc.SpFlag.tri_mul_diag (adj_tri hB) (fun p q h => hB p q h) i
    rw [e, adj_dg] at d
    unfold PD.ψ
    rw [mul_comm, ← d]
    simp
end
