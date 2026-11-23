module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle585
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactModNearOfFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle007
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.PositionTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem eventually_factor {S : Set (Pl E)} {P : Slot S → Prop}
    (h₁ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S, P (Sum.inl ⟨w, hw⟩))
    (h₂ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S ∧ IsSplitAt w, P (Sum.inr ⟨w, hw⟩)) :
    ∀ᶠ i : Slot S in cofinite, P i := by
  have f₁ := Filter.eventually_cofinite.1 h₁
  have f₂ := Filter.eventually_cofinite.1 h₂
  refine Filter.eventually_cofinite.2 ?_
  refine (((f₁.preimage (Subtype.val_injective (p := fun w => w ∈ S)).injOn).image Sum.inl).union
    ((f₂.preimage (Subtype.val_injective (p := fun w => w ∈ S ∧ IsSplitAt w)).injOn).image Sum.inr)).subset ?_
  rintro (⟨w, hw⟩ | ⟨w, hw⟩) hi
  · exact Or.inl ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩
  · exact Or.inr ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩

def localLevel {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem exists_factor_level₂ {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, o₁, e₁, i₁⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₂
  have c₁ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁
  have c₂ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂
  refine ⟨localLevel L₁ L₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | w)
    · exact o₁ w.1
    · exact o₂ w.1
  · exact eventually_factor (e₁.mono fun w h _ => h) (e₂.mono fun w h _ => h)
  · rintro (w | w) k hk x
    · exact (i₁ w.1 k hk x).2
    · exact (i₂ w.1 k hk x).2
  · rintro (w | w)
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₁ w.1
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₂ w.1
  · exact eventually_factor (c₁.mono fun w h _ => h) (c₂.mono fun w h _ => h)

end GlobalTheory.CompanionTheory.PositionTest

end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.StrongUnip

open GlobalTheory.UnipFlagCore (fam wt raise fam_st)
open GlobalTheory.UAut

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def adjF : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (Af F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (Af F)) * cT (sigR (Af F) σ) X * J.map (inclR (F := F) (Af F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def finM : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  RingHom.mapMatrix (finT (F := F) (E := E)).toRingHom

omit [NumberField E] in
theorem finM_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin n) : finM X i j = finT (X i j) := rfl

omit [NumberField E] in
theorem finT_inclR (x : E) : finT (inclR (F := F) (AF F) x) = inclR (F := F) (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem finT_sigR (x : AF F ⊗[F] E) : finT (sigR (AF F) σ x) = sigR (Af F) σ (finT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem finM_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : finM (adjA σ J X) = adjF σ J (finM X) := by
  have a : ∀ M : Matrix (Fin n) (Fin n) E, finM (M.map (inclR (F := F) (AF F))) = M.map (inclR (F := F) (Af F)) :=
    fun M => by
      ext i j
      rw [finM_apply, Matrix.map_apply, Matrix.map_apply, finT_inclR]
  have b : finM (cT (sigR (AF F) σ) X) = cT (sigR (Af F) σ) (finM X) := by
    ext i j
    simp only [finM_apply, cT, Matrix.transpose_apply, Matrix.map_apply, finT_sigR]
  rw [adjA_apply, map_mul, map_mul, a, a, b]
  rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = finM (matHom _ σ J g).1 := by
  ext r s
  exact GlobalTheory.AutFunCompare.mat_mapH σ J (sndA F) g r s

end SlopeTestRemainingChoices

theorem strong_approx_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  intro F E _ _ _ _ _ σ hcm n J hJ k Cc hC W hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.UnipFlagCore.conj_invol hcm
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨d, hdd⟩ : ∃ d : Fin k → ℕ, d = fun _ => 0 := ⟨_, rfl⟩
  have hd : ∀ j, d j < 1 := fun j => by rw [hdd]; exact Nat.one_pos
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ Cc L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) Cc L) d 1
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hcontF : Continuous (adjF σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ Cc L hL hC.2 hLL hd
  have hadj1 : adjF σ J 1 = 1 := by
    have h1 := finM_adjA σ J (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ), map_one] at h1
    exact h1.symm
  let fF : GFin σ J → _ := fun g => Units.embedProduct _ (matHom _ σ J g)
  have hfF : Topology.IsInducing fF := Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOW⟩ := Filter.mem_comap.1 (hfF.nhds_eq_comap 1 ▸ hW)
  let G : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → _ := fun x => (x, MulOpposite.op (adjF σ J x))
  have hG : Continuous G := continuous_id.prodMk (MulOpposite.continuous_op.comp hcontF)
  have hD : G ⁻¹' O ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    hG.continuousAt.preimage_mem_nhds (by
      have : G 1 = fF 1 := Prod.ext rfl (by
        show MulOpposite.op (adjF σ J 1) = MulOpposite.op 1
        rw [hadj1])
      rw [this]; exact hO)
  have hproj : ∀ g : GAd σ J, finM (matHom _ σ J g).1 ∈ G ⁻¹' O → projFin σ J g ∈ W := fun g hg => hOW (by
    have e : fF (projFin σ J g) = G (finM (matHom _ σ J g).1) := by
      refine Prod.ext (mat_projFin σ J g) ?_
      show MulOpposite.op (matHom _ σ J (projFin σ J g)⁻¹).1 = MulOpposite.op (adjF σ J _)
      rw [← map_inv, mat_projFin, ← finM_adjA]
      congr 2
      exact (adjA_mat hJ g).symm
    show fF (projFin σ J g) ∈ O
    rw [e]; exact hg)
  obtain ⟨V, hV, H⟩ := compact_mod_near_of_weights (st := adjA σ J) (w := wt d 1)
    (ε := fam (adjA σ J) (idemA Cc L)) (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) hcont (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add (f := _), ← map_add (f := _), add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) he
    (by
      have hu : ∀ j, idemA (F := F) Cc L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin k ⊕ Fin k, Sum.elim (idemA (F := F) Cc L) (fun j => adjA σ J (idemA Cc L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
    finM (adjF σ J) hcontF (finM_adjA σ J) _ hD
  obtain ⟨W₀, hW₀, hW₀V⟩ := exists_entry_nhds V hV
  obtain ⟨K, hK, hKW, hKs⟩ := fine_cover (E := E) W₀ hW₀
  obtain ⟨K', hK', hKD, k1, k2⟩ := H (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun x hx => hW₀V _ fun i j => hKW _ (hx i trivial j trivial))
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA Cc L)) (wt d 1) 0 → unipFlag σ J Cc d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J Cc d → _ := fun m => Units.embedProduct _ (matHom _ σ J m.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hconst : unipFlag σ J Cc d = unipRad σ J Cc := by rw [hdd]; exact unipFlag_const Cc 0
  refine ⟨Subtype.val '' (f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K')),
    (hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_).image
      continuous_subtype_val, fun m hm => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · rw [← hconst] at hm
    have hu := (adjA_mul_self_iff hJ _).2 m.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J m).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 hm⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : (⟨m, hm⟩ : unipFlag σ J Cc d) = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1).1, ?_, (lift k (k1 k hk)).1, ⟨lift k (k1 k hk), ⟨k, hk, rfl⟩, rfl⟩,
      hconst ▸ (lift k (k1 k hk)).2, hproj _ (hKD k hk), congrArg Subtype.val e⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end GlobalTheory.CompanionTheory.StrongUnip

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        have h := isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))
        have hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k)) := by
          ext A
          show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)
          constructor
          · intro hA i _ j _
            exact hA i j
          · intro hA i j
            exact hA i (Set.mem_univ i) j (Set.mem_univ j)
        rw [hSe]
        exact h
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eval_map (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (g : GL n k) (v : V) :
    (f (τ g v)).1.1 1 = (f v).1.1 g := by
  have hf : f (τ g v) = parInd e ρ g (f v) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (f.isIntertwining' g) v
  rw [hf, parInd_apply, one_mul]

theorem eval_unipRad (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (φ : IndSp e ρ)
    (u : unipRad k e) : φ.1.1 (u : GL n k) = φ.1.1 1 := by
  have hp : (u : GL n k) ∈ parab k e := unipRad_le_parab k e u.2
  have hl : leviProj k e ⟨u, hp⟩ = 1 := (coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2
  have hφ := parInd_law e ρ φ ⟨u, hp⟩ 1
  rw [hl] at hφ
  simpa using hφ

def evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : V →ₗ[ℂ] W where
  toFun v := (f v).1.1 1
  map_add' v w := by simp
  map_smul' c v := by simp

theorem twKer_le_ker_evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V}
    {ρ : Representation ℂ (Levi k m) W} (f : τ.IntertwiningMap (parInd e ρ)) :
    twKer τ (unipRad k e) 1 ≤ LinearMap.ker (evalOne e f) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  have hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v := by
    show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1
    rw [eval_map, eval_unipRad e (f v) u]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply,
    Units.val_one, one_smul, sub_self]

def frobMap (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : (_root_.GlobalTheory.SmGL.jac e τ).IntertwiningMap ρ where
  toLinearMap := (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hmem : leviEmb k e g ∈ parab k e := by
      refine mem_parab_iff.2 fun a b i j hab => ?_
      simp [leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
    have hproj : leviProj k e ⟨leviEmb k e g, hmem⟩ = g := by
      funext a
      ext i j
      simp [leviEmb]
    have h := parInd_law e ρ (f v) ⟨leviEmb k e g, hmem⟩ 1
    rw [mul_one, hproj] at h
    have h2 : evalOne e f (τ (leviEmb k e g) v) =
        (deltaHalf k m g : ℂ) • ρ g (evalOne e f v) := (eval_map e f _ v).trans h
    show (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
        (_root_.GlobalTheory.SmGL.jac e τ g (Submodule.Quotient.mk v)) = ρ g (evalOne e f v)
    rw [jac_mk, map_smul]
    change (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • evalOne e f (τ (leviEmb k e g) v) = _
    rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem frobMap_mk (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (v : V) :
    frobMap e f (Submodule.Quotient.mk v) = (f v).1.1 1 := rfl

theorem frobMap_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (hf : ∃ v, f v ≠ 0) : ∃ y, frobMap e f y ≠ 0 := by
  obtain ⟨v, hv⟩ := hf
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h1 := frobMap_mk e f (τ g v)
  rw [hcon, eval_map] at h1
  simpa using h1.symm

theorem surjective_of_ne_zero {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : ∃ y, f y ≠ 0) : Function.Surjective f := by
  haveI := hσ
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · obtain ⟨y, hy⟩ := hf
    exact (hy (by simp [hz])).elim

theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  let f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := f
  obtain ⟨y, hy⟩ := frobMap_ne_zero _ f' hf
  have hs := surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩
  have hq := jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)
  exact Order.one_le_iff_ne_zero.2 hq

end GlobalTheory.CompanionTheory.FrobJm
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.ProdLen

theorem prodFinLen : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  intro F _ _ _ _ ι _ _ α _ _ m _ _ e X _ _ σ hs hi
  have hirr : (piTensor σ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur σ hi fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (m a) F) (KO F (m a)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (X a) (σ a) (hi a)
        (GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible F (m a) (X a) (σ a) (hs a) (hi a)) φ hφ
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength F α ι m e _ (piTensor σ) (isSmooth_piTensor hs)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.CompanionTheory.ProdLen
end
end
