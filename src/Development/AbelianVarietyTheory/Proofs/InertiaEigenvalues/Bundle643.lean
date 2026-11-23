module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle611
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle614
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle615
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Maps (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) : ⨆ f : Maps V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps V w σ) v, act o (f.1 v) ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hs o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps V w σ) ⟨v, rfl⟩
  refine (hi _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (⨆ f : Maps V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w
            (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, h1, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, h1, hf⟩ : Maps V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem exists_comp_ne_zero (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) {X : Type} [AddCommGroup X] [Module ℂ X] (β : V →ₗ[ℂ] X) (hβ : β ≠ 0) :
    ∃ f : Maps V w σ, β ∘ₗ f.1.codRestrict V f.2.1 ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hβ (LinearMap.ext fun φ => ?_)
  have hle : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (LinearMap.ker β).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, LinearMap.congr_fun (hc f) v, rfl⟩
  rw [iSup_range_eq V hs hi w σ h] at hle
  obtain ⟨ψ, h1, h2⟩ := hle φ.2
  obtain rfl : ψ = φ := Subtype.ext h2
  exact h1

end GlobalTheory.LocDual
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisFixedLattice

theorem coordLeft_lTensor {R : Type} [CommRing R] {V M N : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι R V) (f : M →ₗ[R] N) (x : V ⊗[R] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem coordRight_map {R : Type} [CommRing R] {M P N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    {κ : Type} [DecidableEq κ] (b : Module.Basis κ R N) (f : M →ₗ[R] P) (x : M ⊗[R] N) (j : κ) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) j = f (equivFinsuppOfBasisRight b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_ringHom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (a : ℤ_[l]) : f a = g a := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  have e : a = (a.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f e
  have hg := congrArg g e
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

theorem zA_eq_algebraMap_pt (a : ℤ_[l]) : Per.zA l a = algebraMap ℤ_[l] (Ainf l) a :=
  padicInt_ringHom_ext_pt (R := WittVector l (Per.Fl l)) (Per.zA l) _ a

theorem iota_algebraMap_pt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := by
  rw [zA_eq_algebraMap_pt]
  exact GlobalTheory.MemLoc.ULaws.iota_aB C _

def filZero (C : GlobalTheory.MemLoc.Core l) : Submodule ℤ_[l] (Per.Bcris l) where
  carrier := {b | C.ι b ∈ Per.FilD l 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact add_mem ha hb
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul]
    have e : C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := iota_algebraMap_pt C a
    rw [e, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hb

theorem qB_padicInt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.qB (a : ℚ_[l]) = algebraMap ℤ_[l] (Per.Bcris l) a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [iota_algebraMap_pt, ← C.o_sec.z]
  exact C.ι_u _

theorem exists_padicInt_of_norm_le (q : ℚ_[l]) (N : ℕ) (h : ‖q‖ ≤ (l : ℝ) ^ N) :
    ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  rw [inv_mul_le_iff₀ (pow_pos hl N), mul_one]
  exact h

end GlobalTheory.CrisFixedLattice

namespace GlobalTheory.CrisFixedLattice

theorem frobOB_eq_lTensor {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (x : OB l O) : frobOB l O x = (frobB l).toLinearMap.lTensor O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_pow_smul_eq_one_tmul : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ O K _ _ _ _ _ _ _ G _ _ T C z hφ hz
  classical
  rcases subsingleton_or_nontrivial O with hO | hO
  · haveI := Module.subsingleton O (TW (OB l O) T)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free O ↥T.L.T := T.L.free
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bM := Module.Free.chooseBasis O ↥T.L.T
  let eR := TensorProduct.equivFinsuppOfBasisRight (M := OB l O) bM
  let eL := TensorProduct.equivFinsuppOfBasisLeft (N := Per.Bcris l) bO
  let c := fun j i => eL (eR z j) i

  have hcφ : ∀ j i, Per.φB l (c j i) = c j i := by
    intro j i
    have h1 : eR (TWmap (frobOB l O) T z) j = frobOB l O (eR z j) :=
      coordRight_map bM (frobOB l O).toLinearMap z j
    rw [hφ, frobOB_eq_lTensor] at h1
    have h2 : c j i = eL ((frobB l).toLinearMap.lTensor O (eR z j)) i := congrArg (fun w => eL w i) h1
    rw [coordLeft_lTensor] at h2
    exact h2.symm

  let F0 := filZero C
  let RQ : Submodule ℤ_[l] (OB l O) := LinearMap.range (F0.subtype.lTensor O)
  have hsmul : ∀ (o : O) (w : OB l O), w ∈ RQ → o • w ∈ RQ := by
    rintro o _ ⟨y, rfl⟩
    refine ⟨(LinearMap.mulLeft ℤ_[l] o).rTensor _ y, ?_⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have key : ∀ w, w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∀ j, eR w j ∈ RQ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨β, x, hβ, rfl⟩ := hw'
      intro j
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      refine hsmul _ _ ⟨(1 : O) ⊗ₜ[ℤ_[l]] (⟨β, hβ⟩ : F0), ?_⟩
      simp
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | smul o x _ hx => intro j; rw [map_smul, Finsupp.smul_apply]; exact hsmul o _ (hx j)
  have hzR : ∀ j, eR z j ∈ RQ := key z hz
  have hcF : ∀ j i, C.ι (c j i) ∈ Per.FilD l 0 := by
    intro j i
    obtain ⟨y, hy⟩ := hzR j
    have h := coordLeft_lTensor bO F0.subtype y i
    simp only [c]
    rw [← hy, h]
    exact (equivFinsuppOfBasisLeft bO y i).2

  have hq : ∀ j i, ∃ q : ℚ_[l], C.qB q = c j i := fun j i => (hF l C).2.2.2.1 _ (hcφ j i) (hcF j i)
  choose q hqc using hq

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ∑ i, ‖q j i‖) hl1
  have hb : ∀ j i, ‖(l : ℚ_[l]) ^ N * q j i‖ ≤ 1 := fun j i => by
    refine exists_padicInt_of_norm_le _ N (le_trans ?_ hN.le)
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg (q j i))
      (Finset.mem_univ j))
    exact Finset.single_le_sum (fun i _ => norm_nonneg (q j i)) (Finset.mem_univ i)
  let a : _ → _ → ℤ_[l] := fun j i => ⟨(l : ℚ_[l]) ^ N * q j i, hb j i⟩
  have ha : ∀ j i, ((l ^ N : ℕ) : Per.Bcris l) * c j i = algebraMap ℤ_[l] (Per.Bcris l) (a j i) := by
    intro j i
    rw [← qB_padicInt, ← hqc]
    show _ = C.qB ((l : ℚ_[l]) ^ N * q j i)
    rw [map_mul, map_pow, map_natCast, Nat.cast_pow]
  let y : _ → O := fun j => bO.equivFun.symm (a j)
  refine ⟨N, bM.equivFun.symm y, ?_⟩
  apply eR.injective
  ext j : 1
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply eL.injective
  ext i : 1
  have e1 : bM.repr (bM.equivFun.symm y) j = y j := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e1, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul, ha, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  have e2 : bO.repr (y j) i = a j i := by
    simp only [y]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e2, Algebra.smul_def, mul_one]

end GlobalTheory.CrisFixedLattice
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfRinv

theorem rinv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n M : ℕ) (τ : Ainf l) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d') (Ainf l)) (Q : Matrix (Fin d') (Fin d) (Ainf l)), IsUnit (inclW l τ) → IsUnit (Y.map (inclW l)) → Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (A * Q).map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∀ i j, (l : Ainf l) ^ n ∣ (A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j := by
  intro l _ d d' n M τ Y Y' A Q hτ hY hYY' hdiv
  set f : Ainf l →+* WCb l := inclW l with hf
  let I : Ideal (WCb l) := Ideal.span {((l : WCb l)) ^ n}
  let π : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  let fW := (f.mapMatrix : Matrix (Fin d) (Fin d) (Ainf l) →+* Matrix (Fin d) (Fin d) (WCb l))
  let πM := (π.mapMatrix : Matrix (Fin d) (Fin d) (WCb l) →+* Matrix (Fin d) (Fin d) (WCb l ⧸ I))
  have hsm : ∀ {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : R),
      (φ.mapMatrix : Matrix (Fin d) (Fin d) R →+* Matrix (Fin d) (Fin d) S) (c • 1) = φ c • 1 := by
    intro R S _ _ φ c; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  set t : WCb l := f τ ^ M with ht
  have hfτ : fW (τ ^ M • 1) = t • 1 := by rw [hsm, map_pow]

  have h1 : fW Y * fW Y' = t • 1 := by rw [← map_mul, hYY', hfτ]
  obtain ⟨u, hu⟩ := hY
  have hYw : fW Y = (u : Matrix (Fin d) (Fin d) (WCb l)) := hu.symm
  have h2 : fW Y' * fW Y = t • 1 := by
    have e : fW Y' = (↑u⁻¹ : Matrix (Fin d) (Fin d) (WCb l)) * (fW Y * fW Y') := by
      rw [← Matrix.mul_assoc, hYw, Units.inv_mul, Matrix.one_mul]
    rw [e, h1, hYw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

  set s : WCb l ⧸ I := π t with hs
  have hsu : IsUnit s := (hτ.pow M).map π
  have hmod : πM (fW Y * fW (A * Q) - t • 1) = 0 := by
    ext i j
    simp only [πM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hdiv i j))
  rw [map_sub, map_mul, hsm] at hmod
  have hYZ := sub_eq_zero.mp hmod
  have h2b : πM (fW Y') * πM (fW Y) = s • 1 := by rw [← map_mul, h2, hsm]
  have hZ : πM (fW (A * Q)) = πM (fW Y') := by
    have : s • πM (fW (A * Q)) = s • πM (fW Y') := by
      calc s • πM (fW (A * Q)) = (πM (fW Y') * πM (fW Y)) * πM (fW (A * Q)) := by
              rw [h2b, Matrix.smul_mul, Matrix.one_mul]
        _ = πM (fW Y') * (s • 1) := by rw [Matrix.mul_assoc, hYZ]
        _ = s • πM (fW Y') := by rw [Matrix.mul_smul, Matrix.mul_one]
    exact (hsu.smul_left_cancel).mp this
  have hfin : πM (fW (A * (Q * Y) - τ ^ M • 1)) = 0 := by
    rw [← Matrix.mul_assoc, map_sub, map_sub, map_mul, map_mul, hZ, h2b, hfτ, hsm, sub_self]
  intro i j
  have hij : π (f ((A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j)) = 0 := by
    have := congrFun (congrFun hfin i) j
    simpa [πM, fW, RingHom.mapMatrix_apply, Matrix.map_apply] using this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hij)
  obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) n w (fun _ => ⟨(A * (Q * Y) - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j, by rw [one_mul, ← hw, sub_self]; exact dvd_zero _⟩)
  refine ⟨a, GlobalTheory.Prism.inclW_injective ?_⟩
  rw [one_mul] at ha
  rw [map_mul, map_pow, map_natCast, ← ha]
  exact hw

end GlobalTheory.AinfRinv
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatLevel

theorem hLat_mul_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  intro D V β Λ hΛ L y k hk
  have h : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  have hq : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ St β := parLev_St h.1
  have hf : (1 : Bridge.Gf V).1 = Formalism.UG.bc (inclR (F := D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (1 : GL (Fin V.rank) D.host.E) := by
    rw [map_one]; exact OneMemClass.coe_one _
  have e := GlobalTheory.HLatMove.hLat_mul hΛ 1 y k 1 hf hq
  rw [one_mul] at e
  rw [e]
  ext x
  simp
end GlobalTheory.HLatLevel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.map_mt_mul_left_adelicMatrix_haar_eq : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D V.rank m)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D V.rank m => (HMul.hMul (mt V g) (x : Matrix (Fin V.rank) (Fin m) (AE D)) : Mx D V.rank m)) = μ := by
  first | exact @GlobalTheory.map_mt_mul_eq | exact GlobalTheory.map_mt_mul_eq | (intros; apply GlobalTheory.map_mt_mul_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.map_mul_right_unitaryGram_adelicMatrix_haar_eq : ∀ (D : D7) (N m : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 → ∀ (g : HA (AF D.host.F) D.sp.cm.sig K) (μ : Measure (Mx D m N)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m N => (HMul.hMul (x : Matrix (Fin m) (Fin N) (AE D)) ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) : Mx D m N)) = μ := by
  first | exact @GlobalTheory.mul_unitary_map_haar | exact GlobalTheory.mul_unitary_map_haar | (intros; apply GlobalTheory.mul_unitary_map_haar <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.hodgeTateJumpsReading_rowAdm : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  first | exact @GlobalTheory.AdmReadBridge.main | exact GlobalTheory.AdmReadBridge.main | (intros; apply GlobalTheory.AdmReadBridge.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.ramified_coefficient_chains_of_hypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F → RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK := by
  first | exact @GlobalTheory.theoremC_of_admitted_inputs | exact GlobalTheory.theoremC_of_admitted_inputs | (intros; apply GlobalTheory.theoremC_of_admitted_inputs <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.ExpansionsOdd.main | exact GlobalTheory.ExpansionsOdd.main | (intros; apply GlobalTheory.ExpansionsOdd.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  first | exact @GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | exact GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | (intros; apply GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  first | exact @GlobalTheory.AmbWT.main | exact GlobalTheory.AmbWT.main | (intros; apply GlobalTheory.AmbWT.main <;> assumption)
end
