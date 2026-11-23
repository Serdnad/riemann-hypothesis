module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle812
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

namespace GlobalTheory.NPin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



structure Pin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) where
  cf : CharFrame D
  C : NChoice D
  tp : TupTied D cf C
  chr : NCharTied D cf C tp
  val : ValLL0 D cf
  Q_eq : ∀ i, D.nd.Q i = C.Q (D.nd.w i)
  T : WDTie D.nd D.naut
  lab : LabTrue D T
  cg : CGTrue hL D T
  M : MtFam D
  H : HeckeOpen D M tp.tup
  au : AUTrue hL D T H.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  rep_inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'
  row : ∀ i, RowTrue hL D rep (fun σ w => T.e w (D.naut.locW i σ w)) (D.naut.satW i)
  locW_eq : ∀ i i' σ w, D.naut.locW i σ w = D.naut.locW i' σ w
  jE : D.host.E →+* Qb
  ty : TypesOpen D jE
  wd : WDSide D T
  wdOf : ∀ (i : D.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) w,
    D.naut.wdOf i r w = wd.wdOf (D.nd.l i) (D.naut.iotaQC i) r w ∧
    (D.naut.IsCrysW i r w ↔ wd.IsCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsPotCrysW i r w ↔ wd.IsPotCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsdRW i r w ↔ wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    ∀ τ, D.naut.jumpsW i r τ = wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ

def rcAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls π.toIrrRep)

def IsComp {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E))
    (ξ : (w.adicCompletion E)ˣ →* ℂˣ) : Prop :=
  IsSmoothChar ξ ∧ ∀ x : Eˣ, ξ (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom x) = χ.locK w x

def MtForm (D : D7) (M : MtFam D) (i : D.nd.Loc) : Prop :=
  ∃ B : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ⋆[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] ℂ,
    (∀ f ∈ NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ, ∀ f' ∈ NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ,
      B f f' = starRingEnd ℂ (B f' f) ∧ (f ≠ 0 → 0 < (B f f).re) ∧
        ∀ h, B (NG.rt D.host.E D.R.nV h f) (NG.rt D.host.E D.R.nV h f') = B f f') ∧
    ∀ x y, inner ℂ x y = B ((M.loc i).real x) ((M.loc i).real y)

structure RowMod (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) : Type 1 where
  A : Type
  [acg : AddCommGroup A]
  [mod : Module ℂ A]
  ρ : GAf D.host.E D.R.r →* Module.End ℂ A
  C : Submodule ℂ A
  B : A → A → ℂ
  lin : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z
  herm : ∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)
  pos : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re
  stab : ∀ h, ∀ x ∈ C, ρ h x ∈ C
  inv : ∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y
  smooth : ∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → ρ κ x = x
  adm : ∀ N : ℕ, 0 < N →
    FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → ρ κ x = x})
  φ : D.what₂.Mj j →ₗ[ℂ] A
  φ_mem : ∀ y, φ y ∈ C
  φ_inner : ∀ x y, inner ℂ x y = B (φ x) (φ y)
  isot : ∀ σ y, y ∈ D.what₂.isot j σ ↔ φ y ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) ρ C (rep σ)

attribute [instance] RowMod.acg RowMod.mod

def IsLinAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ} {Ω : Type} [AddCommGroup Ω] [Module ℂ Ω]
    (ω : GAf E n × GAf E r →* Module.End ℂ Ω) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω) : Prop :=
  ∃ c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E, Continuous c ∧
    (∀ x : E, c (s.i x) = algebraMap E (s.w.adicCompletion E) x) ∧
    ∀ (h : GAf E n) (g : GAf E r), TrivOutside {s.v} h → TrivOutside {s.v} g →
      ∀ Φ Φ' : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)),
      (Φ' : Matrix (Fin n) (Fin r) (s.w.adicCompletion E) → ℂ) =
        om μ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ →
      ω (h, g) (ι Φ) =
        ((η (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • ι Φ'

structure ThetaMod (D : D7) (M : MtFam D) (i : D.nd.Loc) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) : Type 1 where
  Ω : Type
  [acg : AddCommGroup Ω]
  [mod : Module ℂ Ω]
  ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω
  Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ
  inv : ∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) (y y' : ↥X.C),
    (F' : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
    Λ (ω (h, g) φ) F' y' = Λ φ F y
  φ₀ : Ω
  read : ∀ x y (F : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)),
    (F : GAf D.host.E D.R.nV → (M.loc i).wt.W) = (M.loc i).real x →
    inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩
  loc : ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
    φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.NPin

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3.FamModel

open _root_.Formalism.L2.Col

theorem nb_congr {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {P : Ideal (𝓞 E)} {s y : List ℕ}
    (f : inType P s ≃ₗ[𝓞 E] inType P y) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : d.inertSet P s = d.inertSet P y := by
  ext d'
  simp only [DecoSet.inertSet, Set.mem_ofPred_eq, IsInertNbr]
  constructor
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f⟩, ⟨e₂.trans f⟩⟩, hf, hb⟩
  · rintro ⟨⟨⟨e₁⟩, ⟨e₂⟩⟩, hf, hb⟩
    exact ⟨⟨⟨e₁.trans f.symm⟩, ⟨e₂.trans f.symm⟩⟩, hf, hb⟩

theorem op_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : Col.GSD K} (c : Col.DecoPts S E n ST SG)
    (P : HeightOneSpectrum (𝓞 E)) (s : List ℕ) :
    (Col.heckeI c P.asIdeal s).op = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
  obtain ⟨y, hy₁, hy₂, ⟨f⟩⟩ := GlobalTheory.InertTypeIso.inType_iso_sorted_pos P.asIdeal s
  have hnb : ∀ d, c.nbI P.asIdeal s d = c.nbI P.asIdeal y d := by
    intro d
    rw [DecoPts.nbI, DecoPts.nbI, DecoSet.inertNb, DecoSet.inertNb, nb_congr f]
  have hop : (Col.heckeI c P.asIdeal s).op = (Col.heckeI c P.asIdeal y).op := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply, heckeI_op_apply, hnb]
  by_cases hlen : 2 * y.length ≤ n
  · exact Or.inr ⟨y, ⟨hy₁, hy₂, hlen⟩, hop⟩
  · left
    rw [hop]
    refine LinearMap.ext fun φ => Subtype.ext (funext fun d => ?_)
    rw [heckeI_op_apply]
    have hempty : c.nbI P.asIdeal y d = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => hlen ?_
      rw [DecoPts.mem_nbI, DecoSet.inertNb] at he
      split_ifs at he with hfin
      · exact GlobalTheory.InertRank.two_mul_length_le P y (c.pts d) (c.pts e) hy₂ (hfin.mem_toFinset.mp he)
      · simp at he
    simp [hempty]

theorem csd_zero_or {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    [StarRing E] {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))} (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG')
    (SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) (Q : offSubI ST SG SG' S0) (s : List ℕ) :
    heckeCSDI S h c SG S0 (Q, s) = 0 ∨ ∃ y, Col.InertTypeOk n y ∧ heckeCSDI S h c SG S0 (Q, s) = heckeCSDI S h c SG S0 (Q, y) := by
  rcases op_zero_or c (offSubI.lev Q).1 s with h0 | ⟨y, hy, hyeq⟩
  · left
    simp only [heckeCSDI, Col.heckeFamI]
    rw [h0, map_zero]
  · right
    refine ⟨y, hy, ?_⟩
    simp only [heckeCSDI, Col.heckeFamI]
    rw [hyeq]

theorem rank_rows (R : Ranks) : R.N R.m - 1 = R.r + R.m * R.t := by
  have hm := R.two_le_m
  simp only [Ranks.N, Ranks.r, Nat.mul_succ]
  generalize R.m * R.t = x
  omega

theorem inertJunk_col {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) := by
  refine { R := ?_, L := ?_ }
  · intro t Q s
    rcases csd_zero_or (Col.mtildeKGSD W Ch sel t.1) (Col.mtildeKOk W Ch sel t.1 hX) (formPts _ _) Pr.vGs S0 Q s with
      h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · refine Or.inr ⟨y, ?_, hyeq⟩
      show Col.InertTypeOk (R.r + R.m * R.t) y
      rw [← rank_rows R]
      exact hy
  · intro j t Q s
    rcases csd_zero_or (Col.mtKGSD W Ch sel t.1 (j.1 + 1)) (Col.mtKOk W Ch sel t.1 hX (j.1 + 1)) (formPts _ _) Pr.vGs S0
        Q s with h | ⟨y, hy, hyeq⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, hy, hyeq⟩

section Real

open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

variable {A3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Real

end GlobalTheory.Hk3.FamModel

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace GlobalTheory.ContraPair.Model

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def sc (χ : HChar E) (o : Op E a) : ℂ := ((opMul χ o : ℂˣ) : ℂ) * opTriv o + opAdd χ o

abbrev line (ha : a ≤ 1) (χ : HChar E) : CuspSub E a := (CuspSub.triv E ha).twist χ

theorem op_line (ha : a ≤ 1) (χ : HChar E) (o : Op E a) (φ : (line ha χ).V) : (line ha χ).op o φ = sc χ o • φ :=
  CuspSub.op_triv_twist ha χ o φ

def gen (ha : a ≤ 1) (χ : HChar E) : (line ha χ).V :=
  (CuspSub.triv E ha).toTwist χ ⟨oneFn E a, Submodule.mem_span_singleton_self _⟩

theorem gen_one (ha : a ≤ 1) (χ : HChar E) : (gen ha χ).1.1 1 = 1 := by
  change (1 : ℂ) * ((chiDet a χ 1 : ℂˣ) : ℂ) = 1
  simp

theorem eq_smul_gen (ha : a ≤ 1) (χ : HChar E) (φ : (line ha χ).V) : φ = φ.1.1 1 • gen ha χ := by
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := ((CuspSub.triv E ha).toTwist χ).surjective φ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  have e : (CuspSub.triv E ha).toTwist χ ⟨c • oneFn E a, hφ⟩ = c • gen ha χ := by
    rw [gen, ← map_smul]; rfl
  rw [e]
  congr 1
  change c = c * (gen ha χ).1.1 1
  rw [gen_one, mul_one]

def ev (π : CuspSub E a) : π.V →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp ((Sm E a).subtype.comp π.V.subtype)

theorem paired_line_iff (ha : a ≤ 1) (χ χ' : HChar E) (s : Op E a → Op E a) :
    Paired (line ha χ) (line ha χ') s ↔ (∀ k, sc χ (.fin k) * sc χ' (s (.fin k)) = 1) ∧
      (∀ k, sc χ (.cpt k) * sc χ' (s (.cpt k)) = 1) ∧ ∀ X, sc χ (.lie X) + sc χ' (s (.lie X)) = 0 := by
  constructor
  · rintro ⟨B, h1, -, h3, h4, h5⟩
    have h0 : B (gen ha χ) (gen ha χ') ≠ 0 := fun h => by
      have := h1 (gen ha χ) fun ψ => by rw [eq_smul_gen ha χ' ψ, map_smul, h, smul_zero]
      have h' := gen_one ha χ
      rw [this] at h'
      exact zero_ne_one h'
    refine ⟨fun k => ?_, fun k => ?_, fun X => ?_⟩
    · have := h3 k (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
    · have := h4 k (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
    · have := h5 X (gen ha χ) (gen ha χ')
      simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ h0 (by linear_combination this)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ (ev _) (ev _), fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
      fun k φ ψ => ?_, fun X φ ψ => ?_⟩
    · have : φ.1.1 1 * (gen ha χ').1.1 1 = 0 := h (gen ha χ')
      rw [gen_one, mul_one] at this
      rw [eq_smul_gen ha χ φ, this, zero_smul]
    · have : (gen ha χ).1.1 1 * ψ.1.1 1 = 0 := h (gen ha χ)
      rw [gen_one, one_mul] at this
      rw [eq_smul_gen ha χ' ψ, this, zero_smul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (sc χ' _), h1, one_mul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (sc χ' _), h2, one_mul]
    · simp only [op_line, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← add_mul, h3, zero_mul]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem toUnits_barK (k : Kinf E a) : Unitary.toUnits (barK k) = invT a (Cinf E) (Unitary.toUnits k) := Units.ext rfl


theorem det_invT {R : Type} [CommRing R] (g : GL (Fin a) R) :
    GeneralLinearGroup.det (invT a R g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  exact Units.ext (Matrix.det_transpose _)

theorem sc_barK (χ : HChar E) (k : Kinf E a) : sc χ (.cpt k) * sc χ (.cpt (barK k)) = 1 := by
  simp only [sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_infGL, toUnits_barK,
    det_invT, map_inv]
  simp

theorem paired_invTOp (ha : a ≤ 1) (χ : HChar E) : Paired (line ha χ) (line ha χ) invTOp := by
  refine (paired_line_iff ha χ χ _).2 ⟨fun k => ?_, fun k => sc_barK χ k, fun X => ?_⟩
  · simp only [invTOp, sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_finGL,
      det_invT, map_inv]
    simp
  · simp only [invTOp, sc, opTriv, opAdd, mul_zero, zero_add]
    change _ + dchi χ (-(Matrix.of X)ᵀ).trace = 0
    rw [Matrix.trace_neg, Matrix.trace_transpose, map_neg, add_neg_cancel]

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem det_map' {R S : Type} [CommRing R] [CommRing S] (c : R →+* S) (k : GL (Fin a) R) :
    GeneralLinearGroup.det (GeneralLinearGroup.map c k) = Units.map c.toMonoidHom (GeneralLinearGroup.det k) :=
  by
  apply Units.ext
  rw [GlobalTheory.CuspRep.det_map]
  rfl

theorem sc_fin (μ : HChar L) (k : GL (Fin a) (Af L)) :
    sc μ (thetaOp (.fin k)) * sc μ (conjOp (.fin k)) = 1 := by
  simp only [thetaOp, conjOp, sc, opMul, opTriv, opAdd, mul_one, add_zero, chiDet, MonoidHom.comp_apply, det_finGL,
    det_thetaGL, map_inv, det_map']
  simp

theorem sc_cpt (μ : HChar L) (k : Kinf L a) :
    sc μ (thetaOp (.cpt k)) * sc μ (conjOp (.cpt k)) = 1 := by
  rw [← sc_barK μ k]
  simp only [thetaOp, conjOp, sc, opMul, map_mul, map_inv, mul_inv_cancel_comm, opTriv, opAdd]

theorem sc_lie (μ : HChar L) (X : Lie L a) :
    sc μ (thetaOp (.lie X)) + sc μ (conjOp (.lie X)) = 0 := by
  simp only [thetaOp, conjOp, sc, opTriv, opAdd, mul_zero, zero_add]
  change dchi μ (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)).trace + _ = 0
  rw [CG.trace_theta, map_neg, neg_add_eq_zero]
  congr 1
  simp [Matrix.trace]

theorem dualIsConjBy_line_iff (ha : a ≤ 1) (μ ψ : HChar L) :
    DualIsConjBy (line ha μ) ψ ↔ IsConjDualBy (line ha μ) ψ := by
  have h0 : IsConjDualBy (line ha μ) ψ ↔ ∀ o : Op L a, sc μ (thetaOp o) = sc (μ * ψ⁻¹) o := by
    rw [IsConjDualBy, ← CuspSub.twist_mul]
    constructor
    · rintro ⟨T, hT⟩ o
      have h := hT o (gen ha μ)
      rw [op_line, op_line, map_smul] at h
      refine smul_left_injective ℂ ((map_ne_zero_iff T T.injective).2 fun e => ?_) h
      have h' := gen_one ha μ
      rw [e] at h'
      exact zero_ne_one h'
    · intro h
      refine ⟨((CuspSub.triv L ha).toTwist μ).symm.trans ((CuspSub.triv L ha).toTwist _), fun o φ => ?_⟩
      rw [op_line, op_line, map_smul, h]
  rw [h0, DualIsConjBy, ← CuspSub.twist_mul, paired_line_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ o
    cases o with
    | fin k => exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (h1 k)) ((sc_fin μ k).trans (h1 k).symm)
    | cpt k => exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (h2 k)) ((sc_cpt μ k).trans (h2 k).symm)
    | lie X => exact add_right_cancel ((sc_lie μ X).trans (h3 X).symm)
  · intro h
    exact ⟨fun k => h _ ▸ sc_fin μ k, fun k => h _ ▸ sc_cpt μ k, fun X => h _ ▸ sc_lie μ X⟩

theorem dualIsConjBy_resReal (μ : HChar L) :
    DualIsConjBy (line le_rfl μ) (compNorm L (GlobalTheory.HeightCounting.Blocks.resReal μ)) := by
  have h := isPolarized_triv (E := L).1.dual
  rw [pow_one, compNorm_quadChar, isConjDualBy_one] at h
  exact (dualIsConjBy_line_iff _ _ _).2 (GlobalTheory.HeightCounting.Blocks.isConjDualBy_resReal h μ)

end GlobalTheory.ContraPair.Model

end
end
