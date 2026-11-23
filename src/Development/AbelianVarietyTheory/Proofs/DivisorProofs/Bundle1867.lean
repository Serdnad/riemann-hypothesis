module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Formalism.LocalToGlobal.Columns.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open MeasureTheory
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriMove

variable {D : D7}

def rdx {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin m) (Fin n) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix id (finCongr h).symm

def rdi {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix (finCongr h).symm id

theorem rdx_rdi {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdx (K := K) h * rdi (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

theorem rdi_rdx {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdi (K := K) h * rdx (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

def glMove {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : GL (Fin m) K) : GL (Fin n) K where
  val := HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h)
  inv := HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q
  val_inv := by
    have e1 := rdx_rdi (K := K) h
    have e2 : (x.1 : Matrix (Fin m) (Fin m) K) * x.2 = 1 := x.val_inv
    calc HMul.hMul (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
          (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
        = HMul.hMul (HMul.hMul P (HMul.hMul (HMul.hMul (x.1 : Matrix (Fin m) (Fin m) K) (HMul.hMul (rdx (K := K) h) (rdi (K := K) h))) (x.2 : Matrix (Fin m) (Fin m) K))) Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, PQ]
  inv_val := by
    have e1 := rdi_rdx (K := K) h
    have e2 : (x.2 : Matrix (Fin m) (Fin m) K) * x.1 = 1 := x.inv_val
    calc HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
          (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
        = HMul.hMul (HMul.hMul (rdi (K := K) h) (HMul.hMul (HMul.hMul (x.2 : Matrix (Fin m) (Fin m) K) (HMul.hMul Q P)) (x.1 : Matrix (Fin m) (Fin m) K))) (rdx (K := K) h) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [QP, Matrix.mul_one, e2, Matrix.mul_one, e1]

variable {S S' T T' : HSp D}

def fP (I : IsoMat S S') : Matrix (Fin S'.rank) (Fin S.rank) (Lev.EAf D) := I.P.map (eToEAf D)

def fQ (I : IsoMat S S') : Matrix (Fin S.rank) (Fin S'.rank) (Lev.EAf D) := I.Q.map (eToEAf D)

theorem fP_fQ (I : IsoMat S S') : fP I * fQ I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fQ_fP (I : IsoMat S S') : fQ I * fP I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.QP, Matrix.map_one _ (map_zero _) (map_one _)]

def betaMove (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) : GL (Fin S'.rank) (Lev.EAf D) :=
  glMove I.rank_eq (fP I) (fQ I) (fP_fQ I) (fQ_fP I) β

def latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E) :=
  Λ.map ((Matrix.mulVecLin I.P).restrictScalars (𝓞 D.host.E))

def cartMove (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * s * I.qT τ

def basMove (I : IsoMat S S') (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * B * rdx I.rank_eq

def rigMove (I : IsoMat S S') (r : Rig S) : Rig S' where
  Λ := latMove I r.Λ
  β := betaMove I r.β
  s τ := cartMove I τ (r.s τ)
  B τ := basMove I τ (r.B τ)

def homMap (IS : IsoMat S S') (IT : IsoMat T T') : WO S T ≃+ WO S' T' where
  toFun x := HMul.hMul (HMul.hMul IT.aP x) IS.aQ
  invFun y := HMul.hMul (HMul.hMul IT.aQ y) IS.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul IT.aQ (HMul.hMul (HMul.hMul IT.aP x) IS.aQ)) IS.aP = x
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aQ IT.aP) x) (HMul.hMul IS.aQ IS.aP) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [IT.aQ_aP, IS.aQ_aP, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul IT.aP (HMul.hMul (HMul.hMul IT.aQ y) IS.aP)) IS.aQ = y
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aP IT.aQ) y) (HMul.hMul IS.aP IS.aQ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [IT.aP_aQ, IS.aP_aQ, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    show HMul.hMul (HMul.hMul IT.aP (x + y)) IS.aQ = HMul.hMul (HMul.hMul IT.aP x) IS.aQ + HMul.hMul (HMul.hMul IT.aP y) IS.aQ
    rw [Matrix.mul_add, Matrix.add_mul]

theorem homMap_apply (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS IT x = HMul.hMul (HMul.hMul IT.aP x) IS.aQ := rfl

def trH (IS : IsoMat S S') (IT : IsoMat T T') (f : WO S T → ℂ) : WO S' T' → ℂ := fun w => f ((homMap IS IT).symm w)

def trLE (IS : IsoMat S S') (IT : IsoMat T T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (homMap IS IT).symm.toEquiv

def omH (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) :=
  (trLE IS IT).conjRingEquiv.toMulEquiv.toMonoidHom.comp (om.comp (IS.kap.symm.toMonoidHom.prodMap IT.kap.symm.toMonoidHom))

theorem omH_apply (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S') (h : GA D T') (f : WO S' T' → ℂ) :
    omH IS IT om (g, h) f = trH IS IT (om (IS.kap.symm g, IT.kap.symm h) (trH IS.symm IT.symm f)) := rfl

def polMove {m n m' n' : ℕ} (hm : m = m') (hn : n = n') :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m' n') ℂ :=
  MvPolynomial.rename fun k => (k.1, finCongr hm k.2.1, finCongr hn k.2.2)

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

def triMove (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) : Tri T₀ A A' WW where
  rA := rigMove IA Y.rA
  rA' := rigMove IA' Y.rA'
  rW := rigMove IW Y.rW
  ω t := omH IA IW (Y.ω t)
  ω' t := omH IA' IW (Y.ω' t)
  vac := trH IA IW Y.vac
  vac' := trH IA' IW Y.vac'
  e := Y.e
  c := Y.c
  f t := trH IA IW (Y.f t)
  f' t := trH IA' IW (Y.f' t)
  m := Y.m.map IA.kap
  fd := IA.kap.symm ⁻¹' Y.fd
  m' := Y.m'.map IA'.kap
  fd' := IA'.kap.symm ⁻¹' Y.fd'

end GlobalTheory.TriMove

end
end

section

set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hP : A.IsForm (A.fn χ * γ) :=
    ((GlobalTheory.T.isForm_one_add_mul_smul M n A).2 0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) :=
    (GlobalTheory.T.holAtlas_isForm_del_dbar_smooth M n A _ hP).2

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dite_eq_right ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.KerAxes.triv_of_memKL_pair | exact GlobalTheory.KerAxes.triv_of_memKL_pair | (intros; apply GlobalTheory.KerAxes.triv_of_memKL_pair <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  first | exact @GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | exact GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm | (intros; apply GlobalTheory.AbDual.memKL_diag_of_triv_ev_of_symm <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  first | exact @GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | exact GlobalTheory.AbDual.memKL_lift_one_of_triv_ev | (intros; apply GlobalTheory.AbDual.memKL_lift_one_of_triv_ev <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  first | exact @GlobalTheory.AbDual.memKL_of_triv_ev_left | exact GlobalTheory.AbDual.memKL_of_triv_ev_left | (intros; apply GlobalTheory.AbDual.memKL_of_triv_ev_left <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_card_mul_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  first | exact @GlobalTheory.change_of_level_classSum | exact GlobalTheory.change_of_level_classSum | (intros; apply GlobalTheory.change_of_level_classSum <;> assumption)
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.classSumMetric_eq_gram_at_infinitePlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  first | exact @GlobalTheory.ClassSumCoord.ipAt_eq_gram | exact GlobalTheory.ClassSumCoord.ipAt_eq_gram | (intros; apply GlobalTheory.ClassSumCoord.ipAt_eq_gram <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.EtaCMType

theorem idFF_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : Fˣ) :
    idFF F E (Units.map (algebraMap F (AF F)).toMonoidHom a) =
      Units.map (incAF F E).toMonoidHom (Units.map (algebraMap F E).toMonoidHom a) := by
  apply Units.ext
  change algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (a : F)) =
    (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E (a : F))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem continuous_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Continuous (idFF F E) := by
  haveI := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E)))

theorem at_idFF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : (AF F)ˣ)
    (h : At (evI F) ((a : AF F) - 1)) :
    At (evI F) (((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) := by
  intro u hu
  have e : ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = algebraMap (AF F) (AF F ⊗[F] E) ((a : AF F) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [e, Algebra.smul_def, ← map_mul, ← smul_eq_mul, h u hu, map_zero]

theorem exists_eta_cmType : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η ∧ ResEtaF η 1 ∧ HasExp B.emb η (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨ξ, hξ, hξe⟩ := GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm F E σ B hB
  obtain ⟨η₀, hη₀, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E hB.cm.2.2.1
  have hη₀' : IsEtaF E η₀ := hη₀
  let lam : (AF F)ˣ →* Circle := ξ.comp (idFF F E) * η₀⁻¹
  have hlam : ∀ a, lam a = ξ (idFF F E a) * (η₀ a)⁻¹ := fun a => rfl
  have hlc : Continuous lam := by
    have : Continuous fun a => ξ (idFF F E a) * (η₀ a)⁻¹ :=
      (hξ.1.comp continuous_idFF).mul (hη₀.1.inv)
    exact this
  have hlF : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1 := by
    intro a
    rw [hlam, idFF_rat, hξ.2, hη₀.2.1, inv_one, one_mul]
  have hlinf : ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1 := by
    intro a ha
    have e1 := hξe _ (at_idFF a ha)
    have e2 := GlobalTheory.T.cmQuadraticCharacter_eq_prod_realSigns F E σ B hB η₀ hη₀' a ha
    have e3 : ξ (idFF F E a) = η₀ a := by
      apply Circle.ext
      rw [e1, e2]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [zpow_one]
    rw [hlam, e3, mul_inv_cancel]
  obtain ⟨lam', hl'H, hl'inf, hl'res⟩ := GlobalTheory.T.exists_unitaryHeckeCharacter_extending_baseCharacter F E σ B hB lam hlc hlF hlinf
  refine ⟨ξ * lam'⁻¹, ⟨hξ.1.mul hl'H.1.inv, fun x => ?_⟩, ⟨⟨η₀, hη₀'⟩, fun η hη a => ?_⟩, fun z hz => ?_⟩
  · change ξ _ * (lam' _)⁻¹ = 1
    rw [hξ.2, hl'H.2, inv_one, one_mul]
  · change ξ _ * (lam' _)⁻¹ = _
    rw [huniq η hη, hl'res, hlam, pow_one, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  · change ((ξ z * (lam' z)⁻¹ : Circle) : ℂ) = _
    rw [hl'inf z hz, inv_one, mul_one]
    exact hξe z hz

end GlobalTheory.EtaCMType
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_frame_of_realization_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → BaseFrT T.toCore R := by
  first | exact @GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn | exact GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn | (intros; apply GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_antiunitary_intertwiner_conjugateEmbedding_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i ((starRingEnd ℂ).comp σ)).H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ y, c τ ((R.MW i σ).rep τ g y) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (c τ y) := by
  first | exact @GlobalTheory.ConjEq.exists_conj_equiv | exact GlobalTheory.ConjEq.exists_conj_equiv | (intros; apply GlobalTheory.ConjEq.exists_conj_equiv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.maximalCompact_acts_on_realVacua_by_detPowers : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ x₁ x₂ y₁ y₂ : D.what₂.Tau → ℤ, (∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * ((1 / 2 : ℂ) • (1 + sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 - sS τ)).det ^ y₁ τ * ((1 / 2 : ℂ) • (1 - sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 + sS τ)).det ^ y₂ τ) • f) := by
  first | exact @GlobalTheory.VacuumChar.vacuum_char | exact GlobalTheory.VacuumChar.vacuum_char | (intros; apply GlobalTheory.VacuumChar.vacuum_char <;> assumption)
end
