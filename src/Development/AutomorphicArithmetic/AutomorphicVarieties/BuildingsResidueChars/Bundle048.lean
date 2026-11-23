module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle053
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIrreducibleSubrepHeckeEigenOfInvariantForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

theorem UpperTheory.mem_iSup_irreducible_of_admissible_unitary :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧ ∀ w, (Set.range fun k : K => ρ k w).Finite) → ∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 := by
  intro H W _ _ _ ρ B hdef hinv hadm x
  classical
  set S : Submodule ℂ W := ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 with hS
  have hSle : ∀ U : Submodule ℂ W, U ≠ ⊥ → (∀ g, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) → U ≤ S := by
    intro U h1 h2 h3
    exact le_iSup (fun U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U} => U.1) ⟨U, h1, h2, h3⟩
  have hSinv : ∀ g, ∀ u ∈ S, ρ g u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (ρ g) := by
      refine iSup_le ?_
      rintro ⟨U, h1, h2, h3⟩ v hv
      exact hSle U h1 h2 h3 (h2 g v hv)
    exact hle hu
  let Z : Subrepresentation ρ := ⟨S, fun g v hv => hSinv g v hv⟩
  let O : Submodule ℂ W := ⨅ z : S, LinearMap.ker (B (z : W))
  have memO : ∀ w, w ∈ O ↔ ∀ z ∈ S, B z w = 0 := by
    intro w
    simp [O, Submodule.mem_iInf]
  let Y : Subrepresentation ρ := ⟨O, fun g v hv =>
    (memO _).2 (GlobalTheory.UnitarySemisimple.orth_stable ρ B hinv Z v ((memO _).1 hv) g)⟩
  obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj ρ B hdef hinv hadm Z x
  by_cases h0 : x - t = 0
  · rw [sub_eq_zero.1 h0]
    exact htS
  exfalso
  let σ : Representation ℂ H O := Y.toRepresentation
  have hσ : ∀ g (v : O), ((σ g v : O) : W) = ρ g v := fun _ _ => rfl
  let B' : O →ₗ⋆[ℂ] O →ₗ[ℂ] ℂ := (B.comp O.subtype).compl₂ O.subtype
  have hB' : ∀ u v : O, B' u v = B u v := fun _ _ => rfl
  have hadm' : ∀ v : O, ∃ K : Subgroup H, (∀ k ∈ K, σ k v = v) ∧
      FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) ∧ ∀ w, (Set.range fun k : K => σ k w).Finite := by
    intro v
    obtain ⟨K, h1, h2, h3⟩ := hadm v
    refine ⟨K, fun k hk => Subtype.ext (h1 k hk), ?_, fun w => ?_⟩
    · let f : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed ρ K :=
        (O.subtype.comp (GlobalTheory.PRep.fixed σ K).subtype).codRestrict _ (by
          intro u k
          exact congrArg Subtype.val (u.2 k))
      refine Module.Finite.of_injective f ?_
      intro a b hab
      have hab' : ((f a : GlobalTheory.PRep.fixed ρ K) : W) = ((f b : GlobalTheory.PRep.fixed ρ K) : W) := by rw [hab]
      exact Subtype.ext (Subtype.ext hab')
    · refine Set.Finite.of_finite_image (f := Subtype.val) ((h3 w).subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  obtain ⟨U, hU, hirr, f, hfU, hf0, -⟩ := UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form H O σ B'
    (fun v hv => Subtype.ext (hdef _ hv)) (fun g u v => hinv g u v) hadm'
    ⟨x - t, (memO _).2 ht⟩ (fun h => h0 (congrArg Subtype.val h))
  have hf0' : (f : W) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfU' : (f : W) ∈ U.map O.subtype := ⟨f, hfU, rfl⟩
  have hle : U.map O.subtype ≤ S := by
    refine hSle _ (fun h => hf0' (by simpa [h] using hfU')) ?_ ?_
    · rintro g _ ⟨u, hu, rfl⟩
      exact ⟨σ g u, hU g u hu, rfl⟩
    · intro N hN hNinv
      have hNO : N ≤ O := hN.trans (Submodule.map_subtype_le _ _)
      have hmc : (N.comap O.subtype).map O.subtype = N := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hNO]
      have hle' : N.comap O.subtype ≤ U := by
        intro u hu
        obtain ⟨w, hw, hwu⟩ := hN hu
        have : w = u := Subtype.ext hwu
        exact this ▸ hw
      rcases hirr _ hle' (fun g u hu => hNinv g u hu) with h | h
      · left
        rw [← hmc, h, Submodule.map_bot]
      · right
        rw [← hmc, h]
  exact hf0' (hdef _ ((memO _).1 f.2 _ (hle hfU')))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_finGL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (k : GL (Fin n) (Af E))
    (hk : ∀ u, cLoc u g = Matrix.GeneralLinearGroup.map (pLoc E u) k) : (g : GA E n) = finGL E n k := by
  have hinf : cInf g = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hg).1
  refine ga_ext (hinf.trans (pInf_finGL k).symm) ?_
  rw [pFin_finGL]
  refine Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)
  exact congrArg Units.val (hk u)

private theorem cLoc_off {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w u : Plc E} {g : UA E n}
    (hg : g ∈ locU n w) (hu : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    cLoc u g = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2 u) hu)

theorem UpperTheory.detCharacter_eq_localDet_split_nonsplit :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ν : HChar E), GlobalTheory.ThetaPull.thetaChar ν = ν → ∀ (w : Plc E), ∀ g ∈ locU n w, (IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n (ν * ν) w (cLoc w g)) ∧ (¬ IsSplitAt w → chiDet n ν (g : UA E n) = CuspSub.locDet n ν w (cLoc w g)) := by
  intro E _ _ _ n ν hν w g hg
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨hne, hun, hover⟩ := GlobalTheory.SplitPts.over_split hw
    set w' := conjSrc (GlobalTheory.SplitPts.conjE E) w with hw'
    have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g) * locGL E n w' (cLoc w' g)) := by
      refine eq_finGL hg _ fun u => ?_
      rw [map_mul]
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]
      · by_cases h2 : u = w'
        · rw [h2, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]
        · rw [pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]
          exact cLoc_off hg fun h => (hover u h).elim h1 h2
    have hd : Units.map (conjLoc (GlobalTheory.SplitPts.conjE E) w).toMonoidHom (Matrix.GeneralLinearGroup.det (cLoc w' g)) =
        (Matrix.GeneralLinearGroup.det (cLoc w g))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
      have h := congrArg Matrix.det (GlobalTheory.SplitPts.comp_eq g w)
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      refine Eq.trans ?_ h
      exact congrArg (· * _) (RingHom.map_det (conjLoc (GlobalTheory.SplitPts.conjE E) w) _)
    have h2 : CuspSub.locDet n ν w' (cLoc w' g) = CuspSub.locDet n ν w (cLoc w g) := by
      change ν.1 (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g))) =
        ν.1 (localIdele E w (Matrix.GeneralLinearGroup.det (cLoc w g)))
      have h3 := GlobalTheory.ThetaPull.thetaChar_apply ν (localIdele E w' (Matrix.GeneralLinearGroup.det (cLoc w' g)))
      rw [hν, GlobalTheory.ThetaPull.conjAd_localIdele, hd, map_inv, map_inv, inv_inv] at h3
      exact h3
    rw [e, map_mul, map_mul, CuspSub.chiDet_locGL, CuspSub.chiDet_locGL, h2]
    rfl
  · have e : (g : GA E n) = finGL E n (locGL E n w (cLoc w g)) := by
      refine eq_finGL hg _ fun u => ?_
      by_cases h1 : u = w
      · rw [h1, pLoc_locGL]
      · rw [pLoc_locGL_of_ne h1]
        exact cLoc_off hg fun h => hw ⟨u, h1, h⟩
    rw [e, CuspSub.chiDet_locGL]
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem infinite_unitary_generated_by_embeddings (s : Finset (InfinitePlace E)) :
    ∀ g ∈ infU E n, (∀ w, w ∉ s → evGL w (cInf g) = 1) → g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg h
    have h2 : GeneralLinearGroup.map (pFin E) g.1 = 1 := hg
    have h1 : cInf g = 1 := gl_ext_evGL fun w => by
      rw [h w (Finset.notMem_empty w), map_one]
    have : g = 1 := by
      refine Subtype.ext (ga_ext ?_ ?_)
      · change cInf g = cInf 1
        rw [h1, map_one]
      · rw [h2]
        exact (map_one _).symm
    rw [this]
    exact one_mem _
  | insert v s hv ih =>
    intro g hg h
    have hr : (embRet v.embedding g : UA E n) ∈ embU n v.embedding := (embRet v.embedding g).2
    have hr' : (embRet v.embedding g : UA E n) ∈ ⨆ τ : E →+* ℂ, embU n τ :=
      (le_iSup (fun τ : E →+* ℂ => embU n τ) v.embedding) hr
    have hk : (embRet v.embedding g : UA E n)⁻¹ * g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
      refine ih _ (mul_mem (inv_mem (embU_le_infU _ hr)) hg) fun w hw => ?_
      rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, InfinitePlace.mk_embedding]
      by_cases e : w = v
      · subst e
        rw [evGL_cutGL_self, inv_mul_cancel]
      · rw [evGL_cutGL_of_ne e, h w (by simp [e, hw]), inv_one, one_mul]
    simpa using mul_mem hr' hk

end

open GlobalTheory.DefU Matrix in
theorem UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), infU E n ≤ (⨆ τ : E →+* ℂ, embU n τ) ∧ ∀ τ τ' : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ a ∈ embU (E := E) n τ, ∀ b ∈ embU n τ', a * b = b * a := by
  intro E _ _ _ n
  refine ⟨fun g hg => infinite_unitary_generated_by_embeddings Finset.univ g hg fun w hw => (hw (Finset.mem_univ w)).elim, ?_⟩
  intro τ τ' hne a ha b hb
  have h2 : GeneralLinearGroup.map (pFin E) b.1 = 1 := hb.1
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * b) = cInf (b * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ'
    · rw [evGL_cInf_of_mem ha (h ▸ hne.symm), one_mul, mul_one]
    · rw [evGL_cInf_of_mem hb h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

private theorem map_iterFrob {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (k : ℕ)
    (x : WittVector p R) :
    WittVector.map (iterateFrobenius R p (k + 1)) x =
      WittVector.frobenius (WittVector.map (iterateFrobenius R p k) x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext i
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

private theorem φB_pow_ιA {l : ℕ} [Fact l.Prime] (k : ℕ) (x : WittVector l (OCb l)) :
    ((PP l).φB ^ k) ((AIP l).ιA x) = (AIP l).ιA (WittVector.map (iterateFrobenius _ l k) x) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change (AIP l).ιA x = _
    congr 1
    ext i
    simp
  | succ k ih =>
    rw [pow_succ', map_iterFrob, (AIP l).ιA_φ, ← ih]
    rfl

open GlobalTheory.UnramifiedRep GlobalTheory.Cyc in
theorem UpperTheory.crystalline_frobenius_algebraic_elements :
    UpperTheory.V.Af.Wd.WittPer := by
  intro l _ K r M hM hMI
  obtain ⟨-, -, hI, -, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  have := compactSpace_GK K
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) ((AIP l).actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq (AIP l) y m hm hy)) M hM
    (fun g hg => hMI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg)))
  have key : ∀ (g : ↥(GK K)) (f : OCb l →+* OCb l) (F : Bcr l → Bcr l),
      (∀ m, 0 < m → ∀ y : OCb l, y ^ l ^ m = y → f y = (AIP l).actT g y) →
      (∀ x, F ((AIP l).ιA x) = (AIP l).ιA (WittVector.map f x)) →
      (M g).map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * ((AIP l).ιA.mapMatrix W).map F =
        (AIP l).ιA.mapMatrix W := fun g f F hf hF => by
    conv_rhs => rw [← hWg g f hf, map_mul]
    congr 1
    · ext i j
      exact (ιA_zlW (AIP l) Ti (M g i j)).symm
    · ext i j
      exact hF _
  refine ⟨(AIP l).ιA.mapMatrix W, ?_, fun g => ?_, fun g k hk => ?_⟩
  · rw [← RingHom.map_det]
    exact hW.map _
  · exact key g ((AIP l).actT g).toRingHom _ (fun _ _ _ _ => rfl) fun x => ((AIP l).ιA_act g x).symm
  · exact key g (iterateFrobenius _ l k) _
      (fun m hm y hy => (UpperTheory.tilt_frobenius_teichmuller_action l y m hm hy g k hk).symm) fun x => φB_pow_ιA k x
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

private theorem count_dims {F D' D D'' : Type} [Field F] [AddCommGroup D'] [Module F D'] [AddCommGroup D] [Module F D]
    [AddCommGroup D''] [Module F D''] (j : D' →ₗ[F] D) (q : D →ₗ[F] D'') (hj : Function.Injective j)
    (hex : Function.Exact j q) (a c : ℕ) (h' : Module.rank F D' ≤ a) (h'' : Module.rank F D'' ≤ c)
    (h : Module.rank F D = (a + c : ℕ)) :
    Module.rank F D' = a ∧ Module.rank F D'' = c ∧ Function.Surjective q := by
  haveI : FiniteDimensional F D' := Module.rank_lt_aleph0_iff.mp (h'.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D'' := Module.rank_lt_aleph0_iff.mp (h''.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI : FiniteDimensional F D := Module.rank_lt_aleph0_iff.mp (h.le.trans_lt (Cardinal.natCast_lt_aleph0))
  rw [← finrank_eq_rank] at h' h'' h
  rw [← finrank_eq_rank, ← finrank_eq_rank]
  have e1 : finrank F D' ≤ a := Nat.cast_le.mp h'
  have e2 : finrank F D'' ≤ c := Nat.cast_le.mp h''
  have e3 : finrank F D = a + c := Nat.cast_injective h
  have e4 := q.finrank_range_add_finrank_ker
  have e5 : finrank F (LinearMap.ker q) = finrank F D' := by
    rw [LinearMap.exact_iff.mp hex, LinearMap.finrank_range_of_inj hj]
  have e6 : finrank F (LinearMap.range q) ≤ finrank F D'' := Submodule.finrank_le _
  refine ⟨by rw [show finrank F D' = a by omega], by rw [show finrank F D'' = c by omega], ?_⟩
  rw [← LinearMap.range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (by omega)

private noncomputable def dmapUr {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' where
  toFun := fun x => toUr P ρ' (dmap P hf ((toUr P ρ).symm x))
  map_add' := fun x y => by simp only [map_add (f := _)]
  map_smul' := fun c x => dmap_mulD P hf c ((toUr P ρ).symm x)

theorem UpperTheory.dpst_right_exact :
    UpperTheory.V.Af.Wd.DRight := by
  intro l _ K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l (UpperTheory.V.Loc.PP l) (UpperTheory.V.Loc.AIP l) (UpperTheory.V.Loc.tiedP l)
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  haveI : FiniteDimensional ℚ_[l] V' := Module.Finite.of_injective (f.restrictScalars ℚ_[l]) hfi
  haveI : FiniteDimensional ℚ_[l] V'' := Module.Finite.of_surjective (p.restrictScalars ℚ_[l]) hps
  obtain ⟨hdi, hdex⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  have h' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ'
  have h'' := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation (UpperTheory.V.Loc.PP l) hdom hreg ρ''
  have hsum : finrank ℚ_[l] V = finrank ℚ_[l] V' + finrank ℚ_[l] V'' := by
    have hexq : Function.Exact (f.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := hex
    have e4 := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
    rw [LinearMap.exact_iff.mp hexq, LinearMap.finrank_range_of_inj (f := f.restrictScalars ℚ_[l]) hfi,
      LinearMap.range_eq_top.mpr (show Function.Surjective (p.restrictScalars ℚ_[l]) from hps), finrank_top] at e4
    omega
  have h : Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr (UpperTheory.V.Loc.PP l) ρ) = (finrank ℚ_[l] V' + finrank ℚ_[l] V'' : ℕ) := by
    rw [← hsum, finrank_eq_rank]; exact hV
  obtain ⟨r1, r2, r3⟩ := count_dims (dmapUr (UpperTheory.V.Loc.PP l) hf) (dmapUr (UpperTheory.V.Loc.PP l) hp) hdi hdex _ _ h' h'' h
  rw [finrank_eq_rank] at r1 r2
  exact ⟨r1, r2, r3⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.traces_from_eigenvalues_rank3 :
    ∀ (q e : ℕ), 1 ≤ q → ∀ D : EigData 3 q ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - ((3 : ℕ) : ℤ)), ∃ (T : TrData q e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum := by
  intro q e hq D
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
  refine ⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩, Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  · intro s
    refine (norm_multiset_sum_le _).trans ?_
    have h := Multiset.sum_le_card_nsmul (((D.β s).map fun b => ((q : ℂ) * b)⁻¹).map fun x => ‖x‖) (1 : ℝ) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hy
      have hp := D.pure s b hb
      have he : (((1 - ((3 : ℕ) : ℤ) : ℤ) : ℝ) / 2) = -1 := by push_cast; norm_num
      rw [he, Real.rpow_neg_one] at hp
      rw [norm_inv, norm_mul, hp, Complex.norm_natCast, mul_inv_cancel₀ hqR.ne', inv_one])
    rw [Multiset.card_map, Multiset.card_map, D.card] at h
    simpa using h
  · intro s
    rw [← Multiset.sum_map_mul_left]
    refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    have h := D.intInv ((e : ℤ) - 1) (by
      intro i
      fin_cases i <;> simp <;> omega) s b hb
    have he : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹ := by
      rw [zpow_sub_one₀ hqC, zpow_natCast, mul_inv, mul_assoc]
    rw [mem_integralClosure_iff, he]
    exact h
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.central_char_sq_eq_of_isSelfDualBy :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (χ : HChar F), π.IsSelfDualBy χ → ∀ (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic π.finPart w σ → ∀ (z : (w.adicCompletion F)ˣ) (c : ℂ), (∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = c • v) → c ^ 2 = ((χ.loc w z : ℂˣ) : ℂ) ^ 2 := by
  intro F _ _ _ π χ hπ w σ hσ z c hc
  obtain ⟨B, d, hl, -, -, hf, -, -⟩ := hπ
  obtain ⟨hnt, htop⟩ := hσ
  set k := locGL F 2 w (Matrix.GeneralLinearGroup.scalar (Fin 2) z) with hk
  have hact : ∀ φ : π.V, π.finPart k φ = c • φ := by
    intro φ
    have hφ : φ ∈ (⊤ : Submodule ℂ π.V) := Submodule.mem_top
    rw [← htop] at hφ
    refine Submodule.iSup_induction _ (motive := fun φ => π.finPart k φ = c • φ) hφ ?_ ?_ ?_
    · rintro f _ ⟨v, rfl⟩
      rw [hk, ← f.2, hc, map_smul]
    · simp
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, smul_add]
  have hop : ∀ φ : π.V, π.op (.fin k) φ = c • φ := fun φ => hact φ
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (hl φ h)
  have h1 := hf k φ ψ
  rw [hop, hop, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
  have h2 := mul_right_cancel₀ hψ h1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two, sq]
  have h3 : chiDet 2 χ (finGL F 2 k) = χ.loc w (z ^ 2) := by
    rw [← hdet]
    exact TR.CuspSub.chiDet_locGL χ w _
  rw [sq, h2, h3, map_pow, Units.val_pow_eq_pow_val]
end
