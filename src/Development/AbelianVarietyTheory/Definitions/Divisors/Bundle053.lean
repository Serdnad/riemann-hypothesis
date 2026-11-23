module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.IsCyclotomicExtensionFourSlopeModelField
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotOntoOfCharAlone
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrimIn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

structure TiesB {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ok : A3.fam3.Ok3 1
  char : R.WeakCharacterisation F
  ex : R.toRealDat.ExAt
  host : Formalism.IndefR.Links.HostHyp D
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  ccK : D.host.ccK = ⊤
  guard : QGuard R.toRealDat
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat
  ser : SerClause D
  junk : GlobalTheory.Hk3.InertJunk A3
  trSem : (∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep
  std : IsStdChar D R.ψ (-1)
  phs : ∀ i, R.phs i = 1
  nV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

end GlobalTheory.PrimIn

end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

open Classical

theorem rank_W_le_V : (Wc D i).rank ≤ (Vc D i).rank :=
  (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le.trans (r_le_V i)

theorem readsOnly_omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) :
    ReadsOnly (R.Pg ∪ Q) (omegaFree R i Q ξR y₀) := by
  intro y y' h
  have hg : ∀ PP ∈ R.Pg, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_left _ hp)
  have hq : ∀ PP ∈ Q, y PP = y' PP := fun PP hp => h PP (Finset.mem_union_right _ hp)
  unfold omegaFree
  congr 1
  · exact if_congr ⟨fun H PP hp => (hg PP hp) ▸ H PP hp, fun H PP hp => (hg PP hp).symm ▸ H PP hp⟩ rfl rfl
  · by_cases H : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det
    · have H' : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun PP hp => (hq PP hp) ▸ H PP hp
      rw [dite_eq_left H, dite_eq_left H']
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (H PP.1 PP.2).unit = (H' PP.1 PP.2).unit := by
        ext; simp [hq PP.1 PP.2]
      rw [this]
    · have H' : ¬ ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y' PP)).det := fun H' =>
        H fun PP hp => (hq PP hp).symm ▸ H' PP hp
      rw [dite_eq_right H, dite_eq_right H']

end GlobalTheory.OnCmp

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG Formalism.IndefR
open GlobalTheory.ChiGrid GlobalTheory.TestLat GlobalTheory.CoefModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj.TestLatModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

theorem finE_rat (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram) (h : Bridge.IsRatMat (Xp G) γ γE.1) :
    Formalism.IndefR.Lev.finE (Xp G) γ = ratIn G γE := by
  have h' : matHom (Xp G) γ = bc (incA D) γE.1 := h
  apply Units.ext
  show ((matHom (Xp G) γ).1.map _).map _ = γE.1.1.map _
  rw [h']
  ext i j
  rfl

theorem map_rhoVr {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (γ : GQ V)
    (γE : GL (Fin V.rank) D.host.E) (h : Bridge.IsRatMat V γ γE) (x : GA D V) (v : VV D.what₂.LL lam) :
    rhoK lam (invTrK (realGL θ V (γ.1 * x)⁻¹)) (mapVV D.what₂.embLL lam (rhoVr (labLL D) lam γE v)) =
      rhoK lam (invTrK (realGL θ V x⁻¹)) (mapVV D.what₂.embLL lam v) := by
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
    funext τ
    apply Units.ext
    rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE h, embGL_inv, ← map_inv, embGL_coe, bc_coe]
    ext a b
    exact hlab _ _
  have e2 : (γ.1 * x)⁻¹ * γ.1 = x⁻¹ := by group
  show rhoK _ _ (mapVV _ _ (rhoK lam (invTrK (embGL (labLL D) γE)) _)) = _
  rw [mapVV_rhoK, e, ← Module.End.mul_apply, ← map_mul (rhoK lam), ← map_mul invTrK, ← map_mul (realGL θ V), e2]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_globLat_rat (γ : GL (Fin n) E) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E) :
    γ.1 *ᵥ x ∈ CS.globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g) Λ ↔ x ∈ CS.globLat g Λ := by
  have e : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [e, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem globLat_mul [StarRing E] (g k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ)) : CS.globLat (g * k) Λ = CS.globLat g Λ := by
  ext x
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]
  exact ((inv_mem hk : k⁻¹ ∈ _) _).symm

end Gen

theorem mem_latOf_rat (γ : UR D.sp.cm (Xp G).gram) (g : GLf G) (x : Fin (Xp G).rank → D.host.E) :
    γ.1.1 *ᵥ x ∈ latOf G (ratIn G γ * g) ↔ x ∈ latOf G g := mem_globLat_rat _ γ.1 g x

theorem latOf_mul (g : GLf G) {k : GLf G} (hk : k ∈ G.Kplus) : latOf G (g * k) = latOf G g :=
  globLat_mul _ g k hk.2.1

theorem exists_testLat (h : (L.ΛY 0).FG) (rp : ClassReps G) : ∃ n e X M, 0 < n ∧ IsTestLat G rp n e X M := by
  obtain ⟨n, ⟨e⟩⟩ := exists_coords G h
  obtain ⟨X, M, hM⟩ := exists_isTestLat G rp n e
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  exact ⟨n, e, X, M, (e.symm (⟨fun _ => default, Quotient.mk'' 1⟩, i)).pos, hM⟩

end GlobalTheory.FunObj.TestLatModel

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

end GlobalTheory.FunObj.SumModel

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn.CoreWit

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.JoinChr in
theorem exists_val_of_chrEq {c : (Formalism.L2.Theta.AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (x : (Formalism.L2.Theta.AE D)ˣ) : ∃ y, ((c x : Circle) : ℂ) = ((χ.1 y : ℂˣ) : ℂ) := by
  have hχ := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.2 c χ h
  obtain ⟨Θ, hc, hinc, hloc⟩ := GlobalTheory.CharTransport.exists_hom D
  let u : (Formalism.L2.Theta.AE D)ˣ →* Neutral.B1.Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c' : (Formalism.L2.Theta.AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have h' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · refine (hcoe _).trans ?_
      have := congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ))
        (Units.ext (hinc x) : u (Units.map (Formalism.L2.Theta.incA D).toMonoidHom x) = Units.map (algebraMap D.host.E _).toMonoidHom x)
      exact this.trans (congrArg (fun y : ℂˣ => (y : ℂ)) (χ.2.2 x))
    · refine (hcoe _).trans (congrArg (fun y => ((χ.1 y : ℂˣ) : ℂ)) (Units.ext ?_))
      change Θ (x : Formalism.L2.Theta.AE D) = _
      rw [hx, hloc P e he]
  exact ⟨u x, by rw [(GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 c c' χ h h', hcoe]⟩

end GlobalTheory.BigOn.CoreWit

end
end
