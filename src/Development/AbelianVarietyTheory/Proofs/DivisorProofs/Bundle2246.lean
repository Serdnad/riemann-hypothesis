module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCobounda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealIndicatorUnitBlockTranslateReadsWeilOpe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem inBlock_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.PGEquiv F → (R.toCx3 F).zs.InBlock := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hC hE hG
  obtain ⟨h1, h2⟩ := GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hL hOk hC hE (schurAll_of_cuspRapidDecay hP R.toRealDat) hG
  have hM := hC.base.models
  refine ⟨fun t x hx => ?_, fun j t x hx => ?_⟩
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HX t
    have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx' : R.jX t x ∈ LinearMap.range (LinearMap.adjoint (R.Th t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.Th t) (R.jX t x)).1 hx
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jX t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h1 t hx')
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L j t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HV j t
    have h := kForm_semi (R.jV j t) (R.HV j t).e (R.B.L j t).pres.extL (fun x => hM.jV j t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx1 := range_adjoint_smul_le (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hx
    have hx' : R.jV j t x ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t x)).1 hx1
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jV j t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h2 j t hx')

end GlobalTheory.Hk3

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  first | exact @GlobalTheory.SymCob.exists_coboundary | exact GlobalTheory.SymCob.exists_coboundary | (intros; apply GlobalTheory.SymCob.exists_coboundary <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblGenV

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem KD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD (g * h) - 1 = matD g * (matD h - 1) + (matD g - 1) := by
      rw [matD_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    show u • (matD (g * h) - 1) = 0
    have h1 : u • (matD h - 1) = 0 := hh.1 u hu
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
    · rw [_root_.mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem KD_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    show u • (matD g⁻¹ - 1) = 0
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem PDiag_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {p : UD σ W} (hp : p ∈ PDiag σ W) :
    p⁻¹ ∈ PDiag σ W := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t⁻¹, ?_⟩
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hDdef
  set T : Matrix (Fin d) (Fin d) (AE F E) := (t : Matrix (Fin d) (Fin d) (AE F E)) with hT
  set Ti : Matrix (Fin d) (Fin d) (AE F E) := ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) with hTi
  have hTT : T * Ti = 1 := by rw [hT, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ht' : matD p * D = D * T := ht
  have key : matD p⁻¹ * (D * T) = D := by
    rw [← ht', ← Matrix.mul_assoc, matD_inv_mul, Matrix.one_mul]
  show matD p⁻¹ * D = D * Ti
  calc matD p⁻¹ * D = matD p⁻¹ * (D * T) * Ti := by
        rw [Matrix.mul_assoc (matD p⁻¹), Matrix.mul_assoc D, hTT, Matrix.mul_one]
    _ = D * Ti := by rw [key]

end GlobalTheory.DblGenV

namespace GlobalTheory.DblGenV

theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B a (a - G.p) G.p G.V hT.base hT.geo.hV v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ a G.V v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

end GlobalTheory.DblGenV
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_localChart_inertPlace_unitaryPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  first | exact @GlobalTheory.InertBridge.exists_chart | exact GlobalTheory.InertBridge.exists_chart | (intros; apply GlobalTheory.InertBridge.exists_chart <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
    ∀ omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁) * z) * Cᵀ)) := by
  first | exact @GlobalTheory.InertLagChar.diagW_omd_point | exact GlobalTheory.InertLagChar.diagW_omd_point | (intros; apply GlobalTheory.InertLagChar.diagW_omd_point <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

theorem _root_.GlobalTheory.T.torsion_frame_abelian_part_torsion_frame : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), NormW U.toUnifPre w₀ ρ → ∀ N : ℕ, 1 ≤ N → ∀ (g o : GtPtF D.toPre F), GtPtF.IsNsmul N g o → o.IsZero → ∀ (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → LiesOver U.toUnifPre w₀ g w x fr → IsTorsFrame A ρ N x fr → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1 := by
  first | exact @GlobalTheory.Poinc.Tors.FrameTors.frame_tors | exact GlobalTheory.Poinc.Tors.FrameTors.frame_tors | (intros; apply GlobalTheory.Poinc.Tors.FrameTors.frame_tors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | exact GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | (intros; apply GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre <;> assumption)
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

theorem sum_mul_right_eq {G M : Type} [Group G] [AddCommMonoid M] (H K : Subgroup G)
    (hn : ∀ g ∈ H, ∀ κ ∈ K, g⁻¹ * κ * g ∈ K) (R : Finset G) (hR : ∀ r ∈ R, r ∈ H)
    (hR2 : ∀ x ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * x ∈ K) (f : G → M) (hf : ∀ x, ∀ κ ∈ K, f (x * κ) = f x)
    (g : G) (hg : g ∈ H) : ∑ r ∈ R, f (r * g) = ∑ r ∈ R, f r := by
  classical
  choose! σ hσ hσu using hR2
  have hmem : ∀ r ∈ R, r * g ∈ H := fun r hr => mul_mem (hR r hr) hg
  refine Finset.sum_nbij (fun r => σ (r * g)) (fun r hr => (hσ _ (hmem r hr)).1) ?_ ?_ ?_
  · intro r1 h1 r2 h2 e
    simp only at e
    have a1 := (hσ _ (hmem r1 h1)).2
    have a2 := (hσ _ (hmem r2 h2)).2
    rw [e] at a1
    have h3 : g⁻¹ * (r1⁻¹ * r2) * g ∈ K := by
      have := mul_mem (inv_mem a1) a2
      simpa [mul_assoc] using this
    have h4 : r1⁻¹ * r2 ∈ K := by
      have := hn g⁻¹ (inv_mem hg) _ h3
      simpa [mul_assoc] using this
    have u1 := hσu r1 (hR r1 h1) r1 ⟨h1, by simpa using K.one_mem⟩
    have u2 := hσu r1 (hR r1 h1) r2 ⟨h2, by simpa using inv_mem h4⟩
    exact u1.trans u2.symm
  · intro r' hr'
    have hx : r' * g⁻¹ ∈ H := mul_mem (hR r' hr') (inv_mem hg)
    obtain ⟨hr, hk⟩ := hσ _ hx
    refine ⟨σ (r' * g⁻¹), hr, ?_⟩
    have h5 : g⁻¹ * (g * r'⁻¹ * σ (r' * g⁻¹)) * g ∈ K := by
      refine hn g hg _ ?_
      have := inv_mem hk
      simpa [mul_assoc] using this
    exact (hσu _ (hmem _ hr) r' ⟨hr', by simpa [mul_assoc] using h5⟩).symm
  · intro r hr
    have := (hσ _ (hmem r hr)).2
    rw [← hf (σ (r * g)) _ this]
    simp

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

theorem congOne_conj {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {g κ : GA D N} (hg : g ∈ intG D N) (hκ : CongOne D 𝔪 κ) :
    CongOne D 𝔪 (g⁻¹ * κ * g) := by
  intro i j
  have e : (((g⁻¹ * κ * g : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((κ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) *
          ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
    have h1 : (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hgi := (mem_intG g).1 hg
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine mul_mem_hatId (hgi l j).1 ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem_hatId (hgi i m).2 (hκ m l)

theorem om_finsum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem stdSum_eig : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  intro D δ t0 hc a d e0 vac had W 𝔪 hm hcop hnu R hR1 hR2 _hfix h hh
  obtain ⟨hhi, hb⟩ := (GlobalTheory.T.mem_blockCongruenceLevelSubgroup_iff_stabilizer_entries D 𝔪 d a h).1 hh
  obtain ⟨c, hc1, k, hk, hk'⟩ := GlobalTheory.T.blockLevel_moves_cosetVector_integral_point D δ t0 hc e0 vac had W 𝔪 hm hcop hnu h hhi hb
  refine ⟨c, hc1, ?_⟩
  have hcv := GlobalTheory.T.unitBlockCosetThetaVector_mem_thetaFunctions D δ hc 𝔪 hm 0 a d e0 vac.1
  have hcong : ∀ x, x ∈ congLev D 𝔪 a ↔ x ∈ intG D a ∧ CongOne D 𝔪 x := GlobalTheory.T.mem_principalCongruenceLevelSubgroup_iff_integral_congruent D 𝔪 a
  unfold stdSum
  rw [om_finsum W 1 h R _ (fun r _ => W.maps _ _ _ hcv), Finset.smul_sum]
  have e1 : ∀ r, W.Om 1 h (W.Om r 1 (cosetV D δ 𝔪 0 a d e0)) = c • W.Om (r * k) 1 (cosetV D δ 𝔪 0 a d e0) := by
    intro r
    have m1 := W.mul 1 r h 1 _ hcv
    have m2 := W.mul r 1 1 h _ hcv
    have m3 := W.mul r k 1 1 _ hcv
    simp only [one_mul, mul_one] at m1 m2 m3
    rw [← m1, m2, hk', W.smul _ _ _ _ (W.maps _ _ _ hcv), ← m3]
  simp_rw [e1]
  refine sum_mul_right_eq (intG D a) (congLev D 𝔪 a) (fun g hg κ hκ => ?_) R hR1 (fun x hx => ?_)
    (fun x => c • W.Om x 1 (cosetV D δ 𝔪 0 a d e0)) (fun x κ hκ => ?_) k hk
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    exact (hcong _).2 ⟨mul_mem (mul_mem (inv_mem hg) h1) hg, congOne_conj hg h2⟩
  · obtain ⟨r, ⟨hr, hrx⟩, hu⟩ := hR2 x hx
    exact ⟨r, ⟨hr, (hcong _).2 ⟨mul_mem (inv_mem (hR1 r hr)) hx, hrx⟩⟩,
      fun r' ⟨hr', h'⟩ => hu r' ⟨hr', ((hcong _).1 h').2⟩⟩
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    have m4 := W.mul x κ 1 1 _ hcv
    rw [mul_one] at m4
    rw [m4, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W 𝔪 hm hcop hnu 0 (by omega) κ h1 h2]

end GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise


theorem _root_.GlobalTheory.T.conjIdealIndicator_unitBlockTranslate_reads_weilOperator : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∀ (G : VC D a d → ℂ) (o : ℕ), Reads ψ θ hS hT ⊤ δ 1 G (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1 (ζ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d)) G)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o))) := by
  first | exact @GlobalTheory.BotSmallTransl.reads_transl | exact GlobalTheory.BotSmallTransl.reads_transl | (intros; apply GlobalTheory.BotSmallTransl.reads_transl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  first | exact @GlobalTheory.SqStepArith.stepFac_ratio | exact GlobalTheory.SqStepArith.stepFac_ratio | (intros; apply GlobalTheory.SqStepArith.stepFac_ratio <;> assumption)
end
