module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle287
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentity
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle254
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle257
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section

namespace GlobalTheory.SuppAtPlace

theorem suppAt_embV : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  intro D V v w h ε he g
  have hP : IsPrimeIdem w ε (ε + cA D ε) := Or.inl ⟨he, rfl⟩
  exact (Supp.suppF_iff_of_isPrimeIdem V hP h _).2 ⟨g, rfl⟩

end GlobalTheory.SuppAtPlace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.datumLevel_hyperspecial_off_finite_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  first | exact @GlobalTheory.FinZeta.LevelOff.level_offS | exact GlobalTheory.FinZeta.LevelOff.level_offS | (intros; apply GlobalTheory.FinZeta.LevelOff.level_offS <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T), levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  first | exact @GlobalTheory.FinZeta.levDatum_ne_zero_spec | exact GlobalTheory.FinZeta.levDatum_ne_zero_spec | (intros; apply GlobalTheory.FinZeta.levDatum_ne_zero_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localProjection_eq_of_idempotent_patch : ∀ {D : D7} (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g k : GA D T) (ε : AE D), compFin D.host.F D.host.E v ε = 1 → Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → projV T v k = projV T v g := by
  first | exact @GlobalTheory.CompIdem.projV_eq_of_idem | exact GlobalTheory.CompIdem.projV_eq_of_idem | (intros; apply GlobalTheory.CompIdem.projV_eq_of_idem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sphericalZetaKernelGL_right_invariant_integral : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w (n := r) → φ (g * k) = φ g := by
  first | exact @GlobalTheory.ZetaGL.kerGL_mul_right_KGL | exact GlobalTheory.ZetaGL.kerGL_mul_right_KGL | (intros; apply GlobalTheory.ZetaGL.kerGL_mul_right_KGL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.Lat

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem gram_reS_eq : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_frameMatrix_mulVec_smul (s' : Fin S.rank → D.host.E) :
    ∑ k, (frP S b *ᵥ s') k • S.frame k = ∑ a, s' a • b a := by
  have hb : ∀ a, b a = ∑ l, frP S b l a • S.frame l := fun a =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b a).symm
  simp only [hb, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem mem_L0c_iff_mem_intVec_of_span_frame (s' : Fin S.rank → D.host.E) : s' ∈ L0c D (reS S b) ↔ frP S b *ᵥ s' ∈ L0c D S := by
  show ∑ a, s' a • b a ∈ S.L0 ↔ ∑ k, (frP S b *ᵥ s') k • S.frame k ∈ S.L0
  rw [sum_frameMatrix_mulVec_smul]

theorem reW_gen (X : AF D.host.F) (a : D.host.E) (t : Fin T.rank → D.host.E) (s' : Fin S.rank → D.host.E) :
    reW S T b (Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
      Matrix.of fun i j => X ⊗ₜ[D.host.F] (a * t i * ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j) := by
  have h0 : ∀ G' : Matrix (Fin S.rank) (Fin S.rank) D.host.E, G' = (frP S b)ᴴ * S.gram * frP S b →
      (star s' ᵥ* G') ᵥ* frPinv S b = star (frP S b *ᵥ s') ᵥ* S.gram := by
    rintro G' rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, frameMatrix_mul_frameMatrixInv, Matrix.mul_one,
      Matrix.star_mulVec, Matrix.vecMul_vecMul]
  have h1 := h0 (reS S b).gram (gram_reS_eq S b)
  have hv : ∀ j, ∑ c, (∑ k, star (s' k) * (reS S b).gram k c) * frPinv S b c j =
      ∑ k, star ((frP S b *ᵥ s') k) * S.gram k j := fun j => congrFun h1 j
  ext i j
  change ∑ c, X ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s' k) * (reS S b).gram k c) * incA D (frPinv S b c j) = _
  rw [Matrix.of_apply, ← hv j, Finset.mul_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  show X ⊗ₜ[D.host.F] _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]

theorem map_latO (LT : Set (Fin T.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    (latO (reS S b) T (L0c D (reS S b)) LT P).map (reWHom S T b) = latO S T (L0c D S) LT P := by
  unfold latO
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨w', ⟨α, hα, hP, a, ha, s', hs', t, ht, rfl⟩, rfl⟩
    exact ⟨α, hα, hP, a, ha, _, (mem_L0c_iff_mem_intVec_of_span_frame S b s').1 hs', t, ht, reW_gen S T b _ a t s'⟩
  · rintro ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    have hs' : frP S b *ᵥ (frPinv S b *ᵥ s) = s := by
      rw [Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    refine ⟨_, ⟨α, hα, hP, a, ha, frPinv S b *ᵥ s, (mem_L0c_iff_mem_intVec_of_span_frame S b _).2 (hs'.symm ▸ hs), t, ht, rfl⟩, ?_⟩
    have key : ∀ s' s : Fin S.rank → D.host.E, frP S b *ᵥ s' = s →
        reW S T b (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a * t i * ∑ k, star (s' k) * (reS S b).gram k j)) =
        Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) := by
      rintro s' s rfl
      exact reW_gen S T b _ a t s'
    exact key _ _ hs'

end GlobalTheory.AdSpan.ReVec.Lat


open GlobalTheory.AdSpan.ReVec.Lat in
theorem GlobalTheory.AdSpan.ReVec.latO_reW_iff : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T),
    u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔
      reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := by
  intro D S T b LT u
  rw [← map_latO S T b LT]
  exact (AddSubgroup.mem_map_iff_mem (f := reWHom S T b) (reW_bijective S T b).1).symm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaAtReframe

section
variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

noncomputable def reFi : (WO (reS S b) T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (reWi S T b)

theorem reWi_add (x y : WO S T) : reWi S T b (x + y) = reWi S T b x + reWi S T b y := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_reWi S T b y, ← reW_add, reWi_reW]

theorem reWi_nsmul (k : ℕ) (x : WO S T) : reWi S T b (k • x) = k • reWi S T b x := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_nsmul, reWi_reW]

theorem isHalf_reWi_iff (e : AE D) (x : WO S T) : IsHalf e (reWi S T b x) ↔ IsHalf e x := by
  have h := isHalf_reW_iff S T b e (reWi S T b x)
  rw [reW_reWi] at h
  exact h.symm

theorem reF_reFi (g : WO (reS S b) T → ℂ) : reF S T b (reFi S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reWi_reW]

theorem reFi_reF (g : WO S T → ℂ) : reFi S T b (reF S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reW_reWi]

theorem heisO_reFi (ψ : AddChar (AF D.host.F) ℂ)
    (hB : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (g : WO (reS S b) T → ℂ) :
    reFi S T b (heisO ψ (reS S b) T u g) = heisO ψ S T (reW S T b u) (reFi S T b g) := by
  have h := heisO_reF S T b ψ hB u (reFi S T b g)
  rw [reF_reFi] at h
  rw [h, reFi_reF]

variable (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T))

theorem isSBHalf_comp_reW (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Φ : WO S T → ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ' (fun x => Φ (reW S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reW_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reW_add, reW_nsmul]
    exact h2 _ ((hΛ u).1 hu) ((isHalf_reW_iff S T b e u).2 hh) _
  · intro t ht
    rw [hΛ, reW_nsmul]
    exact h3 _ ht

theorem isSBHalf_comp_reWi (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Ψ : WO (reS S b) T → ℂ)
    (h : IsSBHalf e Λ' Ψ) : IsSBHalf e Λ (fun x => Ψ (reWi S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reWi_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reWi_add, reWi_nsmul]
    exact h2 _ ((hΛ _).2 (by rwa [reW_reWi])) ((isHalf_reWi_iff S T b e u).2 hh) _
  · intro t ht
    have h4 := (hΛ _).1 (h3 _ ht)
    rwa [reW_nsmul, reW_reWi] at h4

theorem reF_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reF S T b (halfInd e Λ) = halfInd e Λ' := by
  funext x
  simp only [reF, LinearMap.funLeft_apply, halfInd, ← hΛ, isHalf_reW_iff]

theorem reFi_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reFi S T b (halfInd e Λ') = halfInd e Λ := by
  rw [← reF_halfInd S T b e Λ Λ' hΛ, reFi_reF]

end

theorem isThetaAt_reframe : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := by
  intro D ψ S T b e Λ Λ' c f₀ Φ f hB hΛ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  refine ⟨⟨(reF S T b) ∘ₗ Tm ∘ₗ reFi S T b, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro Ψ hΨ x hx
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => Ψ (t + x)) =
          fun s => (fun s' => Ψ (reWi S T b s')) (s + reW S T b x) := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, reWi_add, reWi_reW]
      rw [h1, hTm.trans _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b e x).2 hx), ← heisO_reF S T b ψ hB]
      rfl
    · intro Ψ hΨ y hy
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => ψ (symplO (reS S b) T t y) * Ψ t) =
          fun s => ψ (symplO S T s (reW S T b y)) * (fun s' => Ψ (reWi S T b s')) s := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, hB, reW_reWi]
      rw [h1, hTm.modul _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b _ y).2 hy), ← heisO_reF S T b ψ hB]
      rfl
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, map_smul (reFi S T b),
        reFi_halfInd S T b e Λ Λ' hΛ, hTm.vac]
  · intro Tm' hTm'
    let Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := reFi S T b ∘ₗ Tm' ∘ₗ reF S T b
    have hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => Φ (t + x)) =
            fun s => (fun s' => Φ (reW S T b s')) (s + reWi S T b x) := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, reW_add, reW_reWi]
        rw [h1, hTm'.trans _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b e x).2 hx), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · intro Φ hΦ y hy
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => ψ (symplO S T t y) * Φ t) =
            fun s => ψ (symplO (reS S b) T s (reWi S T b y)) * (fun s' => Φ (reW S T b s')) s := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, hB, reW_reWi]
        rw [h1, hTm'.modul _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b _ y).2 hy), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · simp only [Tm, LinearMap.comp_apply]
        rw [map_smul (reF S T b), reF_halfInd S T b e Λ Λ' hΛ, hTm'.vac, reFi_reF]
    rw [hall Tm hPM]
    exact reF_reFi S T b _

end GlobalTheory.ThetaAtReframe
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SelfDualFrameConj

section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

variable {D : D7}



theorem exists_gfc (V : HSp D) (γ : GL (Fin V.rank) (Ef D)) (hγ : Unimod (OA D) (gramOf V γ)) :
    ∃ k ∈ Formalism.L2.Theta.GfC V, crdLat V V.L0 = lat ((Formalism.IndefR.Lev.finE V k)⁻¹ * γ) := by
  let L : Submodule (𝓞 D.host.E) V.V :=
    (lat γ).comap ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hL : crdLat V L = lat γ := Submodule.map_comap_eq_of_surjective
    (f := (crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).surjective _
  have hm : ∀ x, x ∈ L ↔ crd V x ∈ lat γ := fun _ => Iff.rfl
  have h1 : Submodule.IsLattice D.host.E L := by
    apply Submodule.IsLattice.of_fg D.host.E
    exact Submodule.fg_of_fg_map_injective
      ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).injective
      (hL ▸ (lat_isLattice γ).fg : (crdLat V L).FG)
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    rw [hm, mem_lat_iff_dual hγ]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := (crd V).surjective y
      have := h y hy
      rw [hT_crd D.sp.cm] at this
      exact this
    · intro h y hy
      rw [hT_crd D.sp.cm]
      exact h _ hy
  obtain ⟨k, hkG, hk⟩ := GlobalTheory.VolumeRatioTypings.exists_conj V L h1 h2
  refine ⟨k, hkG, eq_lat (fun x => ?_) (by
    first | exact isLattice_crdLat V V.standardTuple_isLattice | exact isFullLattice_crdLat V)⟩
  have hk' : ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) ↔
      finMat D.sp.cm.sig V.gram k *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (lat γ : Set (Fin V.rank → D.host.E)) := by
    rw [← hL, GlobalTheory.LevelChoices.coe_crdLat]
    have := GlobalTheory.LevelChoices.coe_crdLat (GlobalTheory.VolRatioCompare.reLat V L h1 h2)
    rw [← this] at hk
    exact hk
  refine (hatL_of_hat _ _ _ hk' x).trans ((isFrame_lat γ _).trans ?_)
  rw [mulVec_mulVec, _root_.mul_inv_rev, inv_inv, Units.val_mul]
  rfl

end SlopeTestRemainingChoices

end GlobalTheory.SelfDualFrameConj

theorem GlobalTheory.SelfDualFrameConj.frame_conj : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  intro D V β Λ N h
  obtain ⟨k, hk, hL⟩ := GlobalTheory.SelfDualFrameConj.exists_gfc V β (GlobalTheory.StdFrames.unimod_of_isSD h)
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rw [map_inv, hL]
  exact GlobalTheory.StdFrames.isFrame_lat _
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → R.PGEquiv F → R.PPos := by
  first | exact @GlobalTheory.PosScalRed.posScal_of_galD | exact GlobalTheory.PosScalRed.posScal_of_galD | (intros; apply GlobalTheory.PosScalRed.posScal_of_galD <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical


theorem _root_.GlobalTheory.T.adjointFrameMatrix_add_integral_reduction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  first | exact @GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | exact GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | (intros; apply GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCompact_parahoricLevel_and_contains_lifts : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  first | exact @GlobalTheory.ParahoricCompact.isCompact_flag_and_lift | exact GlobalTheory.ParahoricCompact.isCompact_flag_and_lift | (intros; apply GlobalTheory.ParahoricCompact.isCompact_flag_and_lift <;> assumption)
end
