module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle081
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaCommutant

theorem finrank_eq {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) :
    Module.finrank F (EA P p N) = N ^ P.g := by
  obtain ⟨-, -, hdim, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have h := rank_eq_of_equiv_equiv (R := F) (R' := Γ((Over.mk p).left, ⊤)) σ j.symm σ.bijective
    (fun c w => j.injective (by rw [j.apply_symm_apply, hj, j.apply_symm_apply]))
  have h' : Module.finrank F (EA P p N) = Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) := by
    unfold Module.finrank
    simpa using congrArg Cardinal.toNat h
  rw [h', hdim]

theorem eq_smul_of_commute {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ) (hN : (N : F) ≠ 0) (T : EA P p N →ₗ[F] EA P p N)
    (hT : ∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → IsActOf P.A P.L (N : ℤ) θ (T v).sec (T v').sec) :
    ∃ c : F, ∀ v, T v = c • v := by
  have hN1 : 0 < N := Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero])
  have hfr := finrank_eq P F p N hN
  have hpos : 0 < Module.finrank F (EA P p N) := by rw [hfr]; positivity
  haveI : Module.Finite F (EA P p N) := Module.finite_of_finrank_pos hpos
  haveI : Nontrivial (EA P p N) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 S P F p N hN
  obtain ⟨ρ, hact, -, hsame, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns S P (N : ℤ) (Over.mk p)
  let σ := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (σ c • v) = c • j v := fun _ _ => rfl
  have hσ : ∀ c : F, σ.symm (σ c) = c := σ.symm_apply_apply
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have key := hirr (Module.End.eigenspace T c) fun θ hθ v v' hvv hv => by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    obtain ⟨θ₀, h₀, hcomm⟩ := hT θ.pt hθ
    obtain ⟨u, hu⟩ := hsame θ₀ θ h₀
    have e₁ : ρ θ (j.symm v) = j.symm v' := (hact θ _ _).1 hvv
    have e₂ : IsActOf P.A P.L (N : ℤ) θ₀ v.sec (j (ρ θ₀ (j.symm v))).sec := (hact θ₀ _ _).2 rfl
    have e₃ : ρ θ₀ (j.symm (T v)) = j.symm (T (j (ρ θ₀ (j.symm v)))) := (hact θ₀ _ _).1 (hcomm _ _ e₂)
    have e₄ : v' = σ.symm (u : Γ((Over.mk p).left, ⊤)) • j (ρ θ₀ (j.symm v)) := by
      rw [← hj, σ.apply_symm_apply, ← hu, e₁, j.apply_symm_apply]
    have e₅ : T (j (ρ θ₀ (j.symm v))) = c • j (ρ θ₀ (j.symm v)) := by
      have e₆ : j.symm (c • v) = σ c • j.symm v := rfl
      rw [← j.apply_symm_apply (T (j (ρ θ₀ (j.symm v)))), ← e₃, hv, e₆, map_smul, hj]
    rw [e₄, map_smul, e₅, smul_comm]
  rcases key with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · intro v
    exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)

end GlobalTheory.ThetaCommutant
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSphLat

open GlobalTheory.InertLocField InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_inclR (a : AF F) (e : E) : a • inclR (F := F) (AF F) e = a ⊗ₜ[F] e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem iotaW_toCompl {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (y : Fv F v ⊗[F] E) :
    GlobalTheory.InertBigCell.iotaW hw (toCompl (under_eq_of_isInertAt hw) y) = liftT (E := E) v y := by
  show liftT (E := E) v ((complEquiv hw (under_eq_of_isInertAt hw)).symm
    (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT (E := E) v y
  rw [RingEquiv.symm_apply_apply]

theorem gen_mem {v : Pl (F := F)} {d : ℕ} (W : Spc F E d) {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {y : Fin d → E} (hy : y ∈ W.L) :
    (fun i => GlobalTheory.LatVac.liftV v t ⊗ₜ[F] y i) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩

theorem mem_latAt_iff {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ}
    (W : Spc F E d) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  have liftT_tmul (a : Fv F v) (e : E) :
      liftT (E := E) v (a ⊗ₜ[F] e) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] e := rfl
  have h := under_eq_of_isInertAt hw
  let f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E) :=
    AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)
  have hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := fun _ => rfl
  constructor
  · intro hz
    have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, haO, y, hy, rfl⟩
      refine ⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩
      · have e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) =
            (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) •
              (fun i => algebraMap E (w.adicCompletion E) (y i)) := rfl
        rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      · funext i
        rw [hf]
        dsimp only
        rw [← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]
    obtain ⟨u, hu, e⟩ := AddSubgroup.mem_map.1 (hle hz)
    exact ⟨u, hu, e.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro o
        obtain ⟨t, ht⟩ := _root_.GlobalTheory.LFun.InertChart.toCompl_surjective h (o : w.adicCompletion E)
        have htI : t ∈ intLoc F E v := (mem_intLoc_iff hw h t).2 (ht ▸ o.2)
        have e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) =
            fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i)) := by
          funext i
          rw [hf]
          dsimp only
          rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht,
            show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by
              rw [toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]
        rw [e1]
        refine intLoc_induction (p := fun t => (fun i => liftT (E := E) v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈
          GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI
        · convert gen_mem W ha (W.L.smul_mem x hy) using 1
          funext i
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]
        · convert (zero_mem (GlobalTheory.InertSph.latAt W v)) using 1
          funext i
          simp
        · convert add_mem hp hq using 1
          funext i
          simp [add_mul, map_add (f := _)]
        · convert neg_mem hp using 1
          funext i
          simp [neg_mul, map_neg]
      | zero => intro o; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro o; rw [smul_add, map_add (f := _)]; exact add_mem (hx o) (hy o)
      | smul a x _ hx => intro o; rw [smul_smul]; exact hx (o * a)
    have := key u hu 1
    rw [one_smul] at this
    exact this

end GlobalTheory.InertSphLat
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsFullLattice E → ∀ (v : Pl (F := F)) (p : ℕ), (p : 𝓞 F) ∈ v.asIdeal → ∀ c : AF F, IsUnit c →
    ∀ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - c • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, ∃ y' ∈ GlobalTheory.InertSph.latAt W v, z = M *ᵥ y + p • y') →
    ∃ M' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * M' = 1 ∧ M' * M = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M' *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  exact GlobalTheory.InertSph.exists_inv_keeps_latAt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.SchrFixUniq

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem schr_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (a : ℂ) (φ : (κ → R) → ℂ) : schr ψ w (a • φ) = a • schr ψ w φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem schr_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (φ : (κ → R) → ℂ) : schr ψ 0 φ = φ := by
  funext x
  simp [schr]

theorem char_ne_zero {R : Type} [CommRing R] (ψ : AddChar R ℂ) (x : R) : ψ x ≠ 0 := by
  intro hx
  have h2 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, hx, zero_mul] at h2
  exact one_ne_zero h2

theorem common_eigen {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (S : Set ((κ → R) × (κ → R))) (f g : (κ → R) → ℂ) (hf : ∀ s ∈ S, schr ψ s f = f)
    (hg : ∀ s ∈ S, schr ψ s g = g) (l : (κ → R) × (κ → R)) (hl : l ∈ AddSubgroup.closure S) :
    ∃ χ : ℂ, χ ≠ 0 ∧ schr ψ l f = χ • f ∧ schr ψ l g = χ • g := by
  induction hl using AddSubgroup.closure_induction with
  | mem s hs => exact ⟨1, one_ne_zero, by rw [hf s hs, one_smul], by rw [hg s hs, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [schr_zero', one_smul], by rw [schr_zero', one_smul]⟩
  | add w w' _ _ h h' =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    obtain ⟨χ', hχ', h1', h2'⟩ := h'
    have hz := char_ne_zero ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2))
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ w' φ = χ' • φ →
        schr ψ (w + w') φ = ((ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)))⁻¹ * (χ' * χ)) • φ := by
      intro φ a b
      have e := schr_comp ψ w w' φ
      rw [b, schr_smul', a, smul_smul] at e
      rw [mul_smul, e, smul_smul, inv_mul_cancel₀ hz, one_smul]
    exact ⟨_, mul_ne_zero (inv_ne_zero hz) (mul_ne_zero hχ' hχ), key f h1 h1', key g h2 h2'⟩
  | neg w _ h =>
    obtain ⟨χ, hχ, h1, h2⟩ := h
    have key : ∀ φ : (κ → R) → ℂ, schr ψ w φ = χ • φ → schr ψ (-w) φ = χ⁻¹ • φ := by
      intro φ a
      have e := schr_comp ψ (-w) w φ
      have e0 : ⅟(2 : R) * ((-w).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (-w).2) = 0 := by
        simp
      rw [a, schr_smul', neg_add_cancel, schr_zero', e0, AddChar.map_zero_eq_one, one_smul] at e
      conv_rhs => rw [← e]
      rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    exact ⟨_, inv_ne_zero hχ, key f h1, key g h2⟩

theorem exists_shift {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψk : AddChar (Fv F v) ℂ)
    (hc : Continuous ψk) (h1 : ψk ≠ 1) : ∃ a : Fv F v, a ≠ 0 ∧ ∀ x : Fv F v,
      (∀ y ∈ v.adicCompletionIntegers F, ψk (a * (x * y)) = 1) ↔ x ∈ v.adicCompletionIntegers F := by
  have hne : ∃ t, ψk t ≠ 1 := by
    by_contra h
    push Not at h
    exact h1 (AddChar.ext _ _ fun t => by rw [h t, AddChar.one_apply])
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψk hc hne
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have ha0 : (Valued.v a : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [ha]; exact WithZero.exp_ne_zero
  refine ⟨a, by simpa using ha0, fun x => ?_⟩
  have h := hn (a * x)
  rw [← ha, map_mul, mul_le_iff_le_one_right (zero_lt_iff.2 ha0)] at h
  simpa only [HeightOneSpectrum.mem_adicCompletionIntegers, mul_assoc] using h

theorem exists_pair {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψk : AddChar (Fv F v) ℂ) (hc : Continuous ψk) (h1 : ψk ≠ 1)
    (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v) (hc0 : c ≠ 0)
    (hself : ∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1)
    (hbd : ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F)
    (η : κ → Fv F v) (hη : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) : ∃ y, (η, y) ∈ Λ := by
  classical
  obtain ⟨a, ha, hcond⟩ := exists_shift v ψk hc h1
  let Λ' : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | (w.1, a • w.2) ∈ Λ}
      add_mem' := fun {x y} hx hy => by
        have := Λ.add_mem hx hy
        simpa [smul_add] using this
      zero_mem' := by
        show ((0 : κ → Fv F v), a • (0 : κ → Fv F v)) ∈ Λ
        rw [smul_zero]
        exact Λ.zero_mem
      neg_mem' := fun {x} hx => by
        have := Λ.neg_mem hx
        simpa using this }
  have hΛ' : ∀ w, w ∈ Λ' ↔ (w.1, a • w.2) ∈ Λ := fun _ => Iff.rfl
  have hbd' : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ', ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases (v.adicCompletionIntegers F).mem_or_inv_mem a with h | h
    · refine ⟨a * c, mul_ne_zero ha hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨by rw [mul_assoc]; exact mul_mem h p, ?_⟩
      convert q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · refine ⟨c, hc0, fun l hl i => ?_⟩
      obtain ⟨p, q⟩ := hbd _ ((hΛ' l).1 hl) i
      refine ⟨p, ?_⟩
      convert mul_mem h q using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  obtain ⟨c', hc', hb'⟩ := hbd'
  have hs' : ∀ w, w ∈ Λ' ↔ ∀ l ∈ Λ', (ψk.mulShift a) (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hΛ', hself]
    constructor
    · intro h l hl
      have := h _ ((hΛ' l).1 hl)
      simp only [dotProduct_smul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_sub]
      exact this
    · intro h l hl
      have := h (l.1, a⁻¹ • l.2) (by rw [hΛ']; simpa [smul_smul, mul_inv_cancel₀ ha] using hl)
      rw [AddChar.mulShift_apply, mul_sub] at this
      simp only [dotProduct_smul, smul_eq_mul] at this ⊢
      rwa [mul_inv_cancel_left₀ ha] at this
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (ψk.mulShift a) Λ' c' hc'
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x) hs' hb' η (fun b hb => by
      have := hη _ ((hΛ' _).1 hb)
      rwa [dotProduct_smul, smul_eq_mul, ← AddChar.mulShift_apply] at this)
  exact ⟨_, (hΛ' _).1 hy⟩

theorem proportional_of_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψk : AddChar (Fv F v) ℂ), Continuous ψk → ψk ≠ 1 →
    ∀ (S : Set ((κ → Fv F v) × (κ → Fv F v))) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v),
    Λ ≤ AddSubgroup.closure S → c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ f g : (κ → Fv F v) → ℂ, (∀ s ∈ S, schr ψk s f = f) → (∀ s ∈ S, schr ψk s g = g) → f ≠ 0 → ∃ a : ℂ, g = a • f := by
  intro F _ _ v κ _ ψk hc h1 S Λ c hS hc0 hself hbd f g hf hg hf0
  classical
  have hall : ∀ l, ∃ χ : ℂ, l ∈ Λ → schr ψk l f = χ • f ∧ schr ψk l g = χ • g := by
    intro l
    by_cases hl : l ∈ Λ
    · obtain ⟨χ, -, h⟩ := common_eigen ψk S f g hf hg l (hS hl)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose χ hχ using hall
  refine GlobalTheory.heisenbergEigen_proportional ψk Λ χ f g (fun l hl ξ => ?_) (fun l hl ξ => ?_) hf0
    (exists_pair v ψk hc h1 Λ c hc0 hself hbd)
  · have := congrFun (hχ l hl).1 ξ
    rw [← invOf_eq_inv]
    exact this
  · have := congrFun (hχ l hl).2 ξ
    rw [← invOf_eq_inv]
    exact this

end GlobalTheory.SchrFixUniq
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiV_ne_one | exact GlobalTheory.PsiNontriv.psiV_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiV_ne_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  first | exact @GlobalTheory.LagLocForm.lagr_local_form | exact GlobalTheory.LagLocForm.lagr_local_form | (intros; apply GlobalTheory.LagLocForm.lagr_local_form <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  first | exact @GlobalTheory.DblVac.kD_stab_latDbl | exact GlobalTheory.DblVac.kD_stab_latDbl | (intros; apply GlobalTheory.DblVac.kD_stab_latDbl <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  first | exact @GlobalTheory.InertLagChar.lagInt_linForm | exact GlobalTheory.InertLagChar.lagInt_linForm | (intros; apply GlobalTheory.InertLagChar.lagInt_linForm <;> assumption)
end
