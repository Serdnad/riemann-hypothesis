module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSmoothAtFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  first | exact @GlobalTheory.SkewAdCover.cover | exact GlobalTheory.SkewAdCover.cover | (intros; apply GlobalTheory.SkewAdCover.cover <;> assumption)
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

namespace GlobalTheory.CentralLevi

theorem exists_unit_smul_of_central : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ f g hg hc
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ f

  let Dα : GL (Fin (r + 1)) (AF F ⊗[F] E) → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun α =>
    ⟨cT (sigR (AF F) σ) (α⁻¹).1, cT (sigR (AF F) σ) α.1,
      by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one],
      by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]⟩
  have hmem : ∀ α, lv α ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := fun α => by
    refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨⟨α, trivial, hlv.onC α⟩, ⟨Dα α, trivial, hlv.onD α⟩⟩
  obtain ⟨B, -, hB⟩ := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg (Fin.last r)) (Finset.mem_singleton_self _)).1
  change GL (Fin (r + 1)) (AF F ⊗[F] E) at B
  change (matHom _ σ J g).1 * adMat F X = adMat F X * B.1 at hB
  have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, f.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ α : GL (Fin (r + 1)) (AF F ⊗[F] E), B.1 * α.1 = α.1 * B.1 := fun α => by
    have e := congrArg (fun h => (matHom _ σ J h).1 * adMat F X) (hc (lv α) (hmem α))
    simp only [map_mul, Units.val_mul] at e
    have e1 : (matHom _ σ J g).1 * (matHom _ σ J (lv α)).1 * adMat F X = adMat F X * (B.1 * α.1) := by
      rw [Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have e2 : (matHom _ σ J (lv α)).1 * (matHom _ σ J g).1 * adMat F X = adMat F X * (α.1 * B.1) := by
      rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hlv.onC, Matrix.mul_assoc]
    have := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) (e1.symm.trans (e.trans e2))
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  obtain ⟨c, hcB⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := B.1) fun t =>
    (hcomm ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩).symm
  have hu : IsUnit c := by
    have h1 := congrFun (congrFun (Units.mul_inv B) 0) 0
    rw [← hcB, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    exact ⟨⟨c, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, ?_⟩
  rw [hB, ← hcB, IsUnit.unit_spec]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

end GlobalTheory.CentralLevi
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacLine

theorem eigen_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (g : (Fin a' × Fin (a + a') → Fv F w) → ℂ), g ∈ SB (Fin a' × Fin (a + a') → Fv F w) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) g (c • g)) →
    ∃ r : ℂ, g = r • G.M'.vac w := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v φ hφ hfix
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  obtain ⟨hvSB, hv0, θ, -, hvac⟩ := hTr.geo.hM'.vac v
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ γ : latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f (cf γ • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf γ h
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B a' (a + a') G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW
        v z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := GlobalTheory.T.exists_second_coordinate_of_orthogonal_selfDual v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf (fun u hu => ?_) φ (G.M'.vac v)
    (fun γ => hloc φ hφ γ (hfix γ γ.2 _ (hvac γ γ.2))) (fun γ => hloc _ hvSB γ (hvac γ γ.2)) hv0
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacLine
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.SplitScalar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open scoped Classical in
theorem proj_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem apply_ne_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (T : G →* Module.End ℂ V) (q : G) {f : V}
    (hf : f ≠ 0) : T q f ≠ 0 := fun h => hf (by
  have e : T q⁻¹ (T q f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← e, h, map_zero])

variable {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem at_inv {JB : Matrix β β (AE F E)} {g : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) : At (evI F) (((g⁻¹).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g⁻¹).1 : Matrix β β (AE F E)) - 1 = -(((g⁻¹).1 : Matrix β β (AE F E)) * ((g.1 : Matrix β β (AE F E)) - 1)) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : ((g⁻¹).1 : Matrix β β (AE F E)) * (g.1 : Matrix β β (AE F E)) = 1 := by
      rw [Subgroup.coe_inv, Units.inv_mul]
    rw [this]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem at_mul {JB : Matrix β β (AE F E)} {g h : UG (cA σ) JB}
    (hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)) (hh : At (evI F) ((h.1 : Matrix β β (AE F E)) - 1)) :
    At (evI F) (((g * h).1 : Matrix β β (AE F E)) - 1) := by
  intro u hu
  have e : ((g * h).1 : Matrix β β (AE F E)) - 1 =
      (g.1 : Matrix β β (AE F E)) * ((h.1 : Matrix β β (AE F E)) - 1) + ((g.1 : Matrix β β (AE F E)) - 1) := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, ← Matrix.mul_smul, hh u hu, hg u hu, Matrix.mul_zero, add_zero]

theorem actB_actB_inv {JB : Matrix β β (AE F E)} (g : UG (cA σ) JB) (x : Matrix α β (AE F E)) :
    actB (cA σ) g (actB (cA σ) g⁻¹ x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem splittings_differ_by_character : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (om ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ →
    IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) →
    ∃ ν : UG (cA σ) JB → ℂ,
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ∀ φ ∈ schA F κ, om g φ = ν g • ω₀ g φ) ∧
      (∀ g h : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) ∧
      ContinuousOn ν {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0 := by
  intro hP F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d om ω₀ hψ hom hω hcont
  have key : ∀ g : UG (cA σ) JB, ∃ z : ℂ, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
      ∀ φ ∈ schA F κ, om g φ = z • ω₀ g φ := by
    intro g
    by_cases hg : At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)
    swap
    · exact ⟨1, fun h => absurd h hg⟩
    have hgi := at_inv hg
    obtain ⟨z, hz⟩ := GlobalTheory.T.unitary_operator_commutes_schrodinger hP F κ ψ hψ (om g * ω₀ g⁻¹)
      (fun φ hφ => hom.pres g _ ((hω _ hgi).1 φ hφ))
      (fun w φ hφ => by
        have e1 : schr ψ w φ = d.rho ψ (d.e.symm w) φ := by simp [Darboux.rho]
        rw [Module.End.mul_apply, Module.End.mul_apply, e1, (hω _ hgi).2.1 _ φ hφ,
          hom.impl g _ _ ((hω _ hgi).1 φ hφ), actB_actB_inv]
        simp [Darboux.rho])
      (fun μ hμ φ hφ => by
        rw [Module.End.mul_apply, hom.unit μ hμ g _ ((hω _ hgi).1 φ hφ), (hω _ hgi).2.2 μ hμ φ hφ])
    refine ⟨z, fun _ φ hφ => ?_⟩
    have := hz (ω₀ g φ) ((hω g hg).1 φ hφ)
    rwa [Module.End.mul_apply, ← Module.End.mul_apply (ω₀ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  choose z hz using key
  by_cases h0 : ∃ φ₀ ∈ schA F κ, φ₀ ≠ 0
  swap
  · push_neg at h0
    refine ⟨fun _ => 1, fun g _ φ hφ => ?_, fun _ _ _ _ => by simp, continuousOn_const, fun _ _ => one_ne_zero⟩
    rw [h0 φ hφ, map_zero, map_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, hne⟩ := h0
  refine ⟨z, hz, fun g h hg hh => ?_, fun g hg => ?_, fun g hg h0 => ?_⟩
  · have hgh := at_mul hg hh
    apply smul_left_injective ℂ (apply_ne_zero ω₀ (g * h) hne)
    show z (g * h) • ω₀ (g * h) φ₀ = (z g * z h) • ω₀ (g * h) φ₀
    rw [← hz _ hgh φ₀ hφ₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz h hh φ₀ hφ₀, map_smul,
      hz g hg _ ((hω h hh).1 φ₀ hφ₀), smul_smul, mul_comm]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (apply_ne_zero ω₀ g hne)
    have hl := proj_mem_adm F κ x
    have c1 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g := hcont _ hl φ₀ hφ₀ g hg
    have c2 : ContinuousWithinAt (fun q => (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀))
        {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} g :=
      (hom.cont _ hl φ₀ hφ₀).continuousWithinAt
    have hx' : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ g φ₀) ≠ 0 := hx
    have c3 := c2.div c1 hx'
    have hq : ∀ q, At (evI F) ((q.1 : Matrix β β (AE F E)) - 1) →
        (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) ≠ 0 →
        z q = (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (om q φ₀) /
          (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (ω₀ q φ₀) := by
      intro q hqS hq0
      rw [hz q hqS φ₀ hφ₀, map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hq0]
    refine c3.congr_of_eventuallyEq ?_ (hq g hg hx')
    filter_upwards [Filter.Tendsto.eventually_ne c1 hx', self_mem_nhdsWithin] with q hq0 hqS
    exact hq q hqS hq0
  · have := hz g hg φ₀ hφ₀
    rw [h0, zero_smul] at this
    exact apply_ne_zero om g hne this

end GlobalTheory.SplitScalar
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResidueEisenstein.FrameLeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem absE_det_of_scalesBy {k : ℕ} {X : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * X = 1)
    {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X γ β) :
    absE F E (Matrix.GeneralLinearGroup.det β) = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F X = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : β.1 = (L * γ0.1.1 * X).map (inclR (F := F) (AF F)) := by
    have := congrArg (adMat F L * ·) e
    have h2 : adMat F L * (adMat F X * β.1) = β.1 := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    rw [h2, hmat] at this
    rw [← this]
    simp only [adMat, Matrix.map_mul, Matrix.mul_assoc]
  set c : E := (L * γ0.1.1 * X).det with hc
  have hd : (Matrix.GeneralLinearGroup.det β).1 = inclR (F := F) (AF F) c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb, hc, RingHom.map_det]
    rfl
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := (Matrix.GeneralLinearGroup.det β).mul_inv
      rw [hd, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim (Matrix.GeneralLinearGroup.det β) 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = Matrix.GeneralLinearGroup.det β from
      Units.ext (by simp [hd])] at this

end GlobalTheory.ResidueEisenstein.FrameLeviFacts

namespace GlobalTheory.ResidueEisenstein


open GlobalTheory.StdPar GlobalTheory.ResLine.LeviFacts in
theorem frame_levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hX : initCols X (Fin.last r) = X := rfl
  have hY : initCols Y (Fin.last r) = Y := rfl
  have hlev : ∀ m ∈ levi σ J X Y {Fin.last r}, m ∈ frameStab σ J X ⊤ ∧ m ∈ frameStab σ J Y ⊤ := fun m hm => by
    simp only [levi, Subgroup.mem_iInf] at hm
    exact hm _ (Finset.mem_singleton_self _)
  refine ⟨fun m hm u hu => conj_mem hW (Fin.last r) (hlev m hm).1 hu,
    fun g hg hm => eq_one h hJ hW (Fin.last r) hg (hlev g hm).2,
    fun u hu => (unipRad_fix hu).trans (by simp), fun m hm => ?_,
    fun γ hγ β e => FrameLeviFacts.absE_det_of_scalesBy (yx h hJ hW) hγ e, inf_le_left,
    (isClosed_levi {Fin.last r} h hJ hW).2⟩
  have h2 : m ∈ ⨅ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
  simp only [Subgroup.mem_iInf] at h2
  obtain ⟨B, hB, e⟩ := h2 _ (Finset.mem_singleton_self _)
  exact ⟨B, e, hB⟩

end GlobalTheory.ResidueEisenstein
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.model_evaluation_bijective_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ModelAdm.model_admissible_iff_evaluation | exact GlobalTheory.ModelAdm.model_admissible_iff_evaluation | (intros; apply GlobalTheory.ModelAdm.model_admissible_iff_evaluation <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.weilRep_smooth_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    (∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) →
      x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v),
        ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁) →
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), ∃ U ∈ 𝓝 (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      ∀ x ∈ U, x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v) → x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v) →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ := by
  first | exact @GlobalTheory.SmoothAtPlace.weil_smooth_at | exact GlobalTheory.SmoothAtPlace.weil_smooth_at | (intros; apply GlobalTheory.SmoothAtPlace.weil_smooth_at <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.torus_action_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  first | exact @GlobalTheory.TorusDilate.main | exact GlobalTheory.TorusDilate.main | (intros; apply GlobalTheory.TorusDilate.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.good_model_evaluation_bijective_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  first | exact @GlobalTheory.InvTame.isTame_inv | exact GlobalTheory.InvTame.isTame_inv | (intros; apply GlobalTheory.InvTame.isTame_inv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.evaluation_automorphism_commutes_schwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e →
    Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) → IsTame F T.symm.toLinearMap := by
  first | exact @GlobalTheory.EvSymmTame.isTame_symm | exact GlobalTheory.EvSymmTame.isTame_symm | (intros; apply GlobalTheory.EvSymmTame.isTame_symm <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem _root_.GlobalTheory.T.weil_eigen_bijective_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | exact GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | (intros; apply GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.exists_moduliPoint_trivSqZeroExt_tangentBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι], Fintype.card ι = Dw.dim → ∃ X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x ∧ Function.Injective (fun M : ι → K => spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  first | exact @GlobalTheory.TanBasis.exists_point_tanBasis | exact GlobalTheory.TanBasis.exists_point_tanBasis | (intros; apply GlobalTheory.TanBasis.exists_point_tanBasis <;> assumption)
end
