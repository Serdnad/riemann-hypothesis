module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle318
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNorms
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle319
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaHalf

variable {D : D7}

theorem isHalf_iff_smul {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem isHalf_mul_left {k m n : ℕ} {e : AE D} (A : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (A * u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.mul_smul, hu]

theorem isHalf_mul_right {k m n : ℕ} {e : AE D} {u : Mx D k m} (B : Mx D m n) (hu : IsHalf e u) :
    IsHalf e (u * B) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [← Matrix.smul_mul, hu]

theorem isHalf_smul {m n : ℕ} {e : AE D} (c : AE D) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (c • u) := by
  rw [isHalf_iff_smul] at hu ⊢
  rw [smul_comm, hu]

theorem isHalf_adj_of_cA {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf (cA D e) z) :
    IsHalf e (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  conv_lhs => rw [← GlobalTheory.DualPairCheck.cA_cA e]
  rw [← map_mul, hz j i]

theorem isHalf_cA_adj {m n : ℕ} {e : AE D} {z : Mx D m n} (hz : IsHalf e z) :
    IsHalf (cA D e) (adj z) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, hz j i]

theorem isHalf_ofAdj {L S : HSp D} {e : AE D} {z : Mx D L.rank S.rank} (hz : IsHalf e (adj z)) :
    IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ hz))

theorem ofAdj_rat_mul_half : ∀ (D : D7) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (e : AE D) (y : WO S L''), (IsHalf (cA D e) y → IsHalf e (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) ∧ (IsHalf e y → IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * y))) := by
  intro D L S L'' τ e y
  exact ⟨fun h => isHalf_ofAdj (isHalf_adj_of_cA (isHalf_mul_left _ h)),
    fun h => isHalf_ofAdj (isHalf_cA_adj (isHalf_mul_left _ h))⟩

end GlobalTheory.KappaHalf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaTheta

theorem isThetaFunO_comp_kappa : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L'' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w))) := by
  intro D ψ L S L'' τ hτ f hf
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  set κ : WO S L'' → WO L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  obtain ⟨hadd, hcont, hrat, -, hsym, hparts⟩ :=
    GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (κ w) (κ w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [hsym]
    push_cast
    ring
  let A : WO S L'' →+ WO L S := AddMonoidHom.mk' κ hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun k M h1 h2 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) ⟨γ, rfl⟩
    show f (κ (ratW L'' S γ + w)) = ψ (-(symplOH S L'' (ratW L'' S γ) w)) * f (κ w)
    have e : κ (ratW L'' S γ) = ratW S L γ' := hγ'.symm
    rw [hadd, ← hH, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hparts u).1 h0)) (κ w)
    unfold heisO at e ⊢
    show ψ (symplOH S L'' w u) * f (κ (w + u)) = f (κ w)
    rw [← e, ← hH, hadd]
    rfl
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => (hparts (M t)).2 (h2 t)
    have := hf.smooth k (A.comp M) (hcont.comp h1) h3 (κ w)
    have heq : (fun t => f (κ (w + M t))) = fun t => f (κ w + A (M t)) :=
      funext fun t => congrArg f (hadd w (M t))
    exact (congrArg (ContDiff ℝ _) heq).mpr this

end GlobalTheory.KappaTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms GlobalTheory.StepData
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LocMod.IntFrameStd

variable {D : D7}

theorem isSelfDualC_of_gram_one {S : HSp D} (hG : S.gram = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) : IsSelfDualC S L := by
  have hm : ∀ x : Fin S.rank → D.host.E, x ∈ Examples₂.stdLat _ ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2,
      fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hLe : L = Examples₂.stdLat _ := by
    ext z
    rw [hL z, hm]
    rfl
  subst hLe
  refine ⟨Examples₂.stdLat_isLattice _, fun y => GlobalTheory.Ker.Inhab.selfDual_diag (fun _ => false) _ (fun i k => ?_) y⟩
  rw [hG, Matrix.one_apply]
  simp [Examples₂.sgn]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocMod.IntFrameStd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section



namespace GlobalTheory.HalfStdFin

theorem exists_reps_half_stdHom : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  classical
  intro D S T Q E₂ _ k hk
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T (Formalism.L2.Col.stdLat D.host.E S.rank)
    (Formalism.L2.Col.stdLat D.host.E T.rank) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg (fun _ => True) k hk
  rw [coe_colStdLat, coe_colStdLat] at h
  let G : WO S T → Prop := fun r => ∃ u ∈ stdHom S T, IsHalf E₂ u ∧ ∃ w ∈ stdHom S T, u = r + k • w
  let pick : WO S T → WO S T := fun r => if hG : G r then hG.choose else 0
  refine ⟨hR.toFinset.image pick, fun u hu hh => ?_⟩
  obtain ⟨r, hr, w, hw, huw⟩ := h u hu
  have hG : G r := ⟨u, hu, hh, w, hw, huw⟩
  obtain ⟨_, hh₀, w₀, hw₀, hu₀w⟩ := hG.choose_spec
  have hp : pick r = hG.choose := dif_pos hG
  have hdiff : u = hG.choose + k • (w - w₀) := by
    rw [hu₀w, smul_sub, huw]; abel
  exact ⟨pick r, Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hr), w - w₀, sub_mem hw hw₀,
    GlobalTheory.HalfLatFin.isHalf_of_nsmul E₂ hk hh hh₀ hdiff, by rw [hp]; exact hdiff⟩

end GlobalTheory.HalfStdFin

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdHomOrth

variable {D : D7}

def finInt (D : D7) : AddSubgroup (AE D) :=
  AddSubgroup.closure {z | ∃ α ∈ intAf D.host.F, ∃ x : D.host.E, IsIntegral ℤ x ∧ z = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x}

theorem gen_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] x : AE D) ∈ finInt D :=
  AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩

theorem star_int {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem incA_eq (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra D.host.F R] (a : R) (e : D.host.E) :
    Algebra.trace R (R ⊗[D.host.F] D.host.E) (a ⊗ₜ[D.host.F] e) =
      a * algebraMap D.host.F R (Algebra.trace D.host.F D.host.E e) := by
  have h1 : a ⊗ₜ[D.host.F] e = a • ((1 : R) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul R (R ⊗[D.host.F] D.host.E) ((1 : R) ⊗ₜ[D.host.F] e) =
      (Algebra.lmul D.host.F D.host.E e).baseChange R := by
    ext x
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem intAf_mul' {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) : a * b ∈ intAf D.host.F :=
  fun w => by rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem coe_mem_intAf (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  intro v
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 D.host.F) D.host.F v r

theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    ψ (pairA D.host.F 0 β) = 1 := by
  have := GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 1 (fun a => by
    have htr : Algebra.trace ℚ D.host.F (a : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) a : ℤ) : ℚ) :=
      (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) a).symm
    rw [mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _) β hβ
  rwa [map_one, mul_one] at this

theorem pairFiniteAdele_zero_mul_pairFiniteAdele_zero (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl

theorem pairFiniteAdele_zero_mul_algebraMap_base (α : Af D.host.F) (q : D.host.F) :
    pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) q =
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) q) :=
  Prod.ext (zero_mul (algebraMap D.host.F (Ainf D.host.F) q)) rfl

theorem incA_mul_mem {e : D.host.E} (he : IsIntegral ℤ e) {z : AE D} (hz : z ∈ finInt D) : incA D e * z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα (he.mul hx)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem cA_mem {z : AE D} (hz : z ∈ finInt D) : cA D z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [cA_tmul]
    exact gen_mem hα (star_int hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_mem' {z w : AE D} (hz : z ∈ finInt D) (hw : w ∈ finInt D) : z * w ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, x', hx', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairFiniteAdele_zero_mul_pairFiniteAdele_zero]
      exact gen_mem (intAf_mul' hα hβ) (hx.mul hx')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem psi_trace {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : AE D} (hz : z ∈ finInt D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E x) := Algebra.isIntegral_trace hx
    rw [trace_tmul, pairFiniteAdele_zero_mul_algebraMap_base]
    exact char_int hψ (intAf_mul' hα (coe_mem_intAf ⟨_, hint⟩))
  | zero => rw [map_zero]; exact AddChar.map_zero_eq_one ψ
  | add x y _ _ hx hy => rw [map_add (f := _), AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx => rw [map_neg, AddChar.map_neg_eq_inv, hx, inv_one]

theorem exists_den {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, IsIntegral ℤ ((d : D.host.E) * f i) := by
  have : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).2 inferInstance
  obtain ⟨y, hy, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (f i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rw [zsmul_eq_mul] at h1
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h1; simpa using h1
  · rw [e] at h1
    have := h1.neg
    simpa using this

theorem exists_den_entries (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s, (d : AE D) * v r s ∈ finInt D := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hx0⟩ := exists_den (D := D) fun _ : Unit => ((a0 : D.host.E))⁻¹
  obtain ⟨e, he, hG⟩ := exists_den (D := D) fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2
  refine ⟨d * e, Nat.mul_pos hd he, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        have h2 : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E y) := y.2
        rw [hy, Algebra.smul_def] at h2
        exact h2
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((e : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul (star_int (hs k)) (hG (k, c))
      have e1 : ((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) = (e : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * e * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e1]
      exact (((hx0 ()).mul hA).mul (ht r)).mul hsum
    rw [Matrix.of_apply, ← map_natCast (incA D) (d * e), incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα hint'
  | zero => intro r s; rw [Matrix.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, mul_neg]; exact neg_mem (hx r s)

theorem exists_nsmul_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∃ M : ℕ, 0 < M ∧ ∀ x ∈ stdHom S T, ∀ w ∈ stdHom S T, ψ (symplO S T x (M • w)) = 1 := by
  intro D ψ hψ S T
  obtain ⟨d, hd, hden⟩ := exists_den_entries S T
  obtain ⟨p, hp, hξ⟩ := exists_den (D := D) fun _ : Unit => D.host.xi0
  obtain ⟨q, hq, hS⟩ := exists_den (D := D) fun i : Fin S.rank × Fin S.rank => S.gram⁻¹ i.1 i.2
  obtain ⟨r, hr, hT⟩ := exists_den (D := D) fun i : Fin T.rank × Fin T.rank => T.gram i.1 i.2
  refine ⟨p * q * r * d * d, by positivity, fun x hx w hw => ?_⟩
  refine psi_trace hψ ?_
  unfold hO
  simp only [Finset.mul_sum]
  refine sum_mem fun a _ => sum_mem fun b _ => sum_mem fun c _ => sum_mem fun e _ => ?_
  have key : incA D D.host.xi0 * (incA D (S.gram⁻¹ a b) * cA D (((p * q * r * d * d) • w) c b) * incA D (T.gram c e) * x e a) =
      incA D ((p : D.host.E) * D.host.xi0) * (incA D ((q : D.host.E) * S.gram⁻¹ a b) * (incA D ((r : D.host.E) * T.gram c e) *
        (cA D ((d : AE D) * w c b) * ((d : AE D) * x e a)))) := by
    rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [key]
  exact incA_mul_mem (hξ ()) (incA_mul_mem (hS (a, b)) (incA_mul_mem (hT (c, e))
    (mul_mem' (cA_mem (hden w hw c b)) (hden x hx e a))))

end GlobalTheory.StdHomOrth
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.AdForm

def intVecSub (D : D7) (n : ℕ) : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun {x y} hx hy k => (hx k).add (hy k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c {x} hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact c.2.mul (hx k)

theorem coe_intVecSub (D : D7) (n : ℕ) : ((intVecSub D n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := rfl

theorem stdHom_map_splitIdem : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  intro D S T a ha u hu
  have h := Formalism.IndefR.Fin.latO_map_splitIdem S T (intVecSub D S.rank) (intVecSub D T.rank) ha
    (u := u) (by rw [coe_intVecSub, coe_intVecSub]; exact hu)
  rw [coe_intVecSub, coe_intVecSub] at h
  exact h

end GlobalTheory.AdForm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.halfA_idempotent_component_cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  first | exact @GlobalTheory.AdForm.CocycleSS.cocycle_trivial | exact GlobalTheory.AdForm.CocycleSS.cocycle_trivial | (intros; apply GlobalTheory.AdForm.CocycleSS.cocycle_trivial <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrime_operators_stepZero_scale_norms : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → RamUnitary D → CoCpt (D.sp.X 0) → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (β : ∀ i, Frame (p i) (D.sp.X 0) (Fin (D.sp.X 0).rank)) (Q : ι → Pair k (Fin (D.sp.X 0).rank)), I.Nodup → (Function.Injective fun i => (p i).v) → (∀ (φ : D.what₂.Mu u) y i, RamAt (β i) (Q i) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∀ η : ι → 𝓀[k]ˣ, (∀ φ : D.what₂.Mu u, ∃ φ' : D.what₂.Mu u, ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ').1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ ∀ φ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u (S φ)).1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y) := by
  first | exact @GlobalTheory.RamStepZero.opsStepZero_norm | exact GlobalTheory.RamStepZero.opsStepZero_norm | (intros; apply GlobalTheory.RamStepZero.opsStepZero_norm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  first | exact @GlobalTheory.SeeSaw.fockRed_uniform | exact GlobalTheory.SeeSaw.fockRed_uniform | (intros; apply GlobalTheory.SeeSaw.fockRed_uniform <;> assumption)
end
