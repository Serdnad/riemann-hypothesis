module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle328
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle343
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def latSD (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : (letI := B.host.cmStar; SDLat B.host.E (B.R.N i)) :=
  letI := B.host.cmStar
  ⟨((I.stp u a i).rep c).1.1.deco.1.N, GlobalTheory.SeamSelfDual.isSDLat_of_isSdLat _
    ⟨((I.stp u a i).rep c).1.1.deco.2.lat, ((I.stp u a i).rep c).1.1.deco.2.uni⟩⟩

def mtOf (a : I.ι) (j : ℕ) : (I.rec7 l Z).Dt →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j

theorem mtOf_factors (u : B.Word) (a : I.ι) : GL3Theta.CarriesTupleCharacters (I.rec7 l Z) ((I.rec7 l Z).chTw u a) (I.mtOf l Z a)
    (fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1) := by
  intro i hi
  have hm : 1 ≤ i + 1 ∧ i + 1 ≤ B.R.m := ⟨by omega, hi⟩
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt_eq]
    simp only [GL3Theta.rhoOf, mtOf, if_pos hm]
    rfl
  · show ((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt'_eq]
    simp only [GL3Theta.rhoOf', mtOf, if_pos hm]
    rfl

def objOf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a) :=
  letI := B.host.cmStar
  { mt := I.mtOf l Z a
    L0 := fun i => ⟨GlobalTheory.Glob.IntegralWittCoefficients.Model.stdLat _ _, GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => GlobalTheory.Glob.IntegralWittCoefficients.Model.mem_stdLat x
    lat := fun i c => I.latSD u a i c
    dt := fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1
    dt_lat := fun i c => GlobalTheory.Mem.Col2.mk_detPt_eq_relDetQ B.R B.host _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1
    c13 := I.mtOf_factors l Z u a
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by
        rintro ⟨y, rfl⟩ τ
        exact (y.2 τ).ne_zero, fun h => ⟨⟨f, fun τ => isUnit_iff_ne_zero.2 (h τ)⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := I.J.cD
    dgen_gen := hok.amb_ok.dgen
    S := insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
    Th := fun i c c' => I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') }

theorem objOf_unf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) :
    UnfIsAll (I.objOf l Z hok Qp u a) i := by
  intro c c' Q
  have e0 : ∀ (n : ℕ) (P : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N n)) ℂ),
      frPoly (I.objOf l Z hok Qp u a) n P = fnOf (Gr B.fields.emb B.embLL (B.R.N n)) 0 1 P := by
    intro n P
    funext y
    simp [frPoly, GL3Theta.evFr, fnOf, objOf]
    rfl
  have e1 : frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    LinearMap.congr_fun (frInv_spec (I.objOf l Z hok Qp u a) hi) Q
  show fnOf _ 0 1 (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 _ _)) 0 (polOf _ 0 (fr0 _ _ _) (frPoly (I.objOf l Z hok Qp u a) i Q))) =
    frPoly (I.objOf l Z hok Qp u a) (i + 1) (jetMap _ _ (frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q)))
  have e2 : polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))
      (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    (congrArg _ (e0 i Q)).trans (GlobalTheory.TilClass.polOf_fnOf_one B.fields.emb B.embLL 0 Q)
  refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1
    (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 P)) e2).trans ?_
  rw [e1, e0 (i + 1)]
  rfl

theorem lift_objects : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ Qp : I.ι → Finset ℕ, ∃ O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a), I.StdO l Z Qp O ∧ ∀ u a i, i < B.R.m → UnfIsAll (O u a) i := by
  intro B X I hok _ l Z Qp
  refine ⟨I.objOf l Z hok Qp, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩, fun u a i hi => I.objOf_unf l Z hok Qp u a i hi.le⟩

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem toCx_smul {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (c : B.LL) (x : (MtHL I hX a).V) :
    toCx I hX a (c • x) = B.embLL c • toCx I hX a x := by
  have h1 : toCx I hX a (c • x) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      (c • (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x)) := rfl
  rw [h1, LinearMap.map_smulₛₗ]
  rfl

theorem toCx_add {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x y : (MtHL I hX a).V) :
    toCx I hX a (x + y) = toCx I hX a x + toCx I hX a y := by
  have h1 : toCx I hX a (x + y) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      ((show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x) + (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from y)) := rfl
  rw [h1, map_add (f := _)]
  rfl

noncomputable def toCxₛₗ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a where
  toFun := toCx I hX a
  map_add' := toCx_add I hX a
  map_smul' := toCx_smul I hX a

theorem toCx_linearIndependent {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) :=
  toMtilde_linearIndependent _ _ _ _ _ _ (MtHL I hX a).b.linearIndependent

theorem toCx_span {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  rw [eq_top_iff, ← toMtilde_span B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL hX, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hle : Submodule.span B.LL (Set.range (MtHL I hX a).b) ≤
      Submodule.comap (toCxₛₗ I hX a) (Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [(MtHL I hX a).b.span_eq] at hle
  exact hle (Submodule.mem_top (x := (x : (MtHL I hX a).V)))

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).Good :=
  MtildeH_good _ _ _ _ _ _
end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good_basis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  intro B X I hX a
  refine ⟨?_, ⟨{ toFun := toCx I hX a, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, fun _ => rfl⟩,
    toCx_linearIndependent I hX a, toCx_span I hX a⟩
  · exact mtHL_good I hX a
  · exact toCx_add I hX a x y
  · exact toCx_smul I hX a c x

end GlobalTheory.Mem.Df
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
open GlobalTheory.TopStep Formalism.HermitianLatticesTheory
noncomputable section

namespace GlobalTheory.Mem.Df

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (C : ChainIn X.E X.K X.Tau R) (b0 : (C.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (C.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (C.S R.m).G b0) (tz : X.E)

@[reducible] def perStepX : PerIn C where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H _ := ⊤

variable (σ : X.K →+* ℂ)

theorem mem_perStepX_Mt (F : ∀ b, (stepX Ch sel mu P).D b → Pol ℂ X.Tau (R.N R.m - 1)) :
    F ∈ (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ ↔
      FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F () (trivPt X _ _ _ _ p) := by
  constructor
  · intro h p
    refine ⟨(h () _).1, fun g hg => ?_⟩
    show F () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (h () (trivPt X _ _ _ _ p)).2 g hg
  · rintro h ⟨⟩ d
    obtain ⟨p, rfl⟩ := (trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).surjective d
    refine ⟨(h p).1, fun g hg => ?_⟩
    exact (congrArg (F ()) (stepX_smul_trivPt Ch sel mu P g p)).trans ((h p).2 g hg)

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

def mtEquivStepX : MtP W Ch sel mu P σ ≃ₗ[ℂ] (perStepX W Ch sel mu P C b0 til ext tz).Mt X.emb σ :=
  LinearEquiv.ofBijective
    { toFun := fun F => ⟨fun _ p => F.1 (toRow sel mu p.1.1),
        (mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ _).2
          ((frLaw_comp_iff σ W.sgTrue (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd F.1).2 F.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨fun F G h => Subtype.ext (funext fun d => by
      obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
      exact congrFun (congrFun (congrArg Subtype.val h) ()) (trivPt X _ _ _ _ p)),
    fun F => by
      obtain ⟨G, hG, e⟩ := ((mem_perStepX_Mt W Ch sel mu P C b0 til ext tz σ F.1).1 F.2).exists_form σ W.sgTrue
        (isSubLev_top (rowTyG Ch P) (levQX R sel mu)) hd
      refine ⟨⟨G, hG⟩, Subtype.ext (funext fun _ => funext fun p => (e p.1.1).trans ?_)⟩
      exact congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p)⟩

end General

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem disjoint_vGs_Q (hI : I.Ok) (l : I.Laws) (a : I.ι) : Disjoint (B.primes X).vGs (I.Q a) :=
  GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup a) l.pr hI.sel_ok (fun i => hI.g_mem i)

theorem mtCx_equiv_per : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  intro B X I hI _ l _ u a
  let g := mtEquivStepX B.wts I.Ch I.sel (I.tup a) I.Ps (I.chIn u a) (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext
    (I.perIn u a).tz B.embLL (disjoint_vGs_Q I hI l a)
  exact ⟨g, fun F p => rfl⟩

end GlobalTheory.Mem.Df

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

theorem exists_int_isDia {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
      ∀ {n f : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
        (S : StepLevel D.host.F D.host.E (sigD D) J (D.mem u).A.T f bad), ∃ δ, IsDia S (A.eV v).1 (A.eV v).2 k δ := by
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied A v
  exact ⟨k, hk, fun S => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond S _ _ k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent S _ _ (D.mem u).A.T_prime k hkT e he hee hσ)⟩



theorem exists_isDia_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : ((I.rec7 l Z).mem u).A.Fv v) = a ∧ (∀ h : i = 0 ∨ i = (I.rec7 l Z).R.m, ∃ δ, IsDia ((F u).cls i hi h).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ) ∧ ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), ∃ δ, IsDia ((F u).ch i h1 h2 β).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ := by
  intro B X I _ _ l Z H F _ _ u i hi v a
  obtain ⟨k, hk, h⟩ := exists_int_isDia (F u).atT v a
  exact ⟨k, hk, fun _ => h _, fun _ _ _ => h _⟩

end GlobalTheory.Mem.Col2.HAt
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PolyId

theorem shiftOf_lamT_succ {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (i : ℕ)
    (hi : i < R.m) (τ : ι) : shiftOf (Col2.lamT hc (i + 1)) τ = -C.sDiv i τ := by
  have hN : R.N (i + 1) = R.k + (i + 1) * (R.t + 1) := rfl
  have h1 : 1 ≤ (i + 1) * (R.t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos : 0 < R.N (i + 1) := by rw [hN]; omega
  have hk : ¬ (R.N (i + 1) - 1 < R.k) := by rw [hN]; omega
  have hq : (R.N (i + 1) - 1 - R.k) / (R.t + 1) = i := by
    rw [hN]
    have hm : (i + 1) * (R.t + 1) = i * (R.t + 1) + R.t + 1 := by ring
    rw [hm, show R.k + (i * (R.t + 1) + R.t + 1) - 1 - R.k = R.t + i * (R.t + 1) by omega,
      Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h2 := C.sDiv_eq i hi τ
  obtain ⟨c, hc'⟩ := R.t_odd
  have hcq : (R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc'
  have e2 : (R.t + 1) / 2 = c + 1 := by omega
  simp only [shiftOf, DomWeight.detShift, dif_pos hpos, Col2.lamT, Col2.shW, Examples₂.lamOf, dif_pos (show i + 1 ≤ R.m by omega), Examples₂.wtQ, dif_neg hk]
  simp only [hq, e2]
  have hw : -wG R ((hc τ).e ⟨i, hi⟩) (i + 1) = ((-C.sDiv i τ + ((i + 1) * (c + 1) : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  rw [hw, Int.floor_intCast]
  push_cast
  ring

theorem secC_eq_of_evC_eq_evV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (z : VV B.LL (lamT (B.hcW u) (i + 1))) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = evV B.fields.emb (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (lamT (B.hcW u) (i + 1)) B.embLL z → ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL)) = (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) := by
  intro B X I hOk hP l Z Qp O hStd u μ i hi z v' h
  have hfun : fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1
      (MvPolynomial.map B.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) =
      fnOf (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb))
      (shiftOf (Col2.lamT (B.hcW u) (i + 1))) 1 (MvPolynomial.map B.embLL z.1) := by
    rw [← evV_apply]
    rw [← h]
    refine Eq.trans ?_ (evC_sec O u μ (i + 1) v').symm
    funext y
    have hfr := hStd.frm u μ (i + 1) y
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL ((secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL))) ((O u μ).frm (i + 1) y)
    rw [hfr]
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, GL3Theta.evFr]
    congr 1
    · refine Finset.prod_congr rfl fun τ _ => ?_
      have hs : shiftOf (Col2.lamT (B.hcW u) (i + 1)) τ = -((I.rec7 l Z).chTw u μ).sDiv i τ :=
        shiftOf_lamT_succ ((I.rec7 l Z).chTw u μ) i hi τ
      rw [hs, Pi.one_apply, Matrix.one_mul]
      rfl
    · simp only [Pi.one_apply, Matrix.one_mul]
      rfl
  have h2 := fnOf_injective _ _ 1 (fun _ => by simp) (stdFrC (n := B.R.N (i + 1)) (embAt B.embLL B.fields.emb)) hfun
  exact MvPolynomial.map_injective _ B.embLL.injective h2

end GlobalTheory.Mem.Col2.PolyId
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_act_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  intro B X I _ l u a j b x p hx
  obtain ⟨γ, κ⟩ := x
  simp only at hx
  subst hx
  exact _root_.GlobalTheory.Mem.Col2.cosetIn_smul_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ rfl rfl

end GlobalTheory.Mem.Col2
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.Mem.Col2

theorem stpTop_groupClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  have hne : B.R.m + 1 ≠ B.R.m := by omega
  have hY : ∀ p : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.2 = ∅ := by
    intro p
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hne] at h
    exact h
  have hpt : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.1 = q.1.1 → p = q := by
    intro p q h
    exact Subtype.ext (Prod.ext h ((hY p).trans (hY q).symm))
  have hcos : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn p = cosetIn q := by
    intro p q
    funext P
    ext z
    simp [cosetIn, hY p, hY q]
  set S := I.stp u a B.R.m with hS
  have key : ∀ (T : GStep B.fields.E B.fields.K (B.R.N B.R.m)) (b : T.β) (x y : T.D b) (g : T.G b), g • x = y →
      (Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) x) = Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) y :=
    fun T b x y g h => Quotient.sound ⟨g⁻¹, by rw [← h]; exact inv_smul_smul g x⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_ | al, hb⟩, q⟩
    · refine ⟨Equiv.refl _, fun κ => ⟨rfl, rfl, rfl, rfl, hcos _ _, fun h => hpt _ _ h⟩⟩
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · rintro ⟨⟨_ | al, hb⟩, q⟩ ⟨⟨_ | al', hb'⟩, q'⟩ γ h θ hγ
    · have e1 : S.act ⟨none, hb⟩ (γ, h, θ) (S.rep ⟨⟨none, hb⟩, q⟩) = S.rep ⟨⟨none, hb'⟩, q'⟩ := hpt _ _ hγ
      have hq : q = q' := by
        have h1 := S.rp_spec ⟨none, hb⟩ q
        have h2 := S.rp_spec ⟨none, hb'⟩ q'
        rw [← h1, ← h2]
        exact key S _ _ _ _ e1
      subst hq
      rfl
    · exact absurd (hb'.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · intro p
    obtain ⟨pt, hpt'⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m) p
    let b : S.β := Idx.top I.sel (I.tup a) (I.idx a) le_rfl
    obtain ⟨g, hg⟩ := S.exists_mv b pt
    refine ⟨S.cl b pt, g.1, g.2.1, g.2.2, ?_⟩
    exact (congrArg (fun x : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m => x.1.1) hg).trans hpt'
  · haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
    obtain ⟨pt, -⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m)
      (DecoF.base _ _ _ _ _)
    exact ⟨S.cl (Idx.top I.sel (I.tup a) (I.idx a) le_rfl) pt⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroCls

theorem stepZeroClassEquiv_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word)
    (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  intro B X I h l u c
  show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep c)) = c
  refine Eq.trans ?_ (GlobalTheory.Mem.Col2.ClsZero.cl_rep _ c)
  refine (GlobalTheory.Mem.Col2.ClsZero.cl_eq_iff h u I.mu0 _ _ _ _).2 ?_
  rfl

end GlobalTheory.Mem.Col2.TC.MuZeroCls
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.couplingCoset_congr_index_frames_localLattices : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_congr | exact GlobalTheory.Mem.Col2.cosetIn_congr | (intros; apply GlobalTheory.Mem.Col2.cosetIn_congr <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  first | exact @GlobalTheory.Mem.Col2.TC.fm_sg_eq | exact GlobalTheory.Mem.Col2.TC.fm_sg_eq | (intros; apply GlobalTheory.Mem.Col2.TC.fm_sg_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cl0_bijective_and_deco_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b, Function.Bijective (I.cl0 u a b) ∧ ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  first | exact @GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | exact GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | (intros; apply GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco <;> assumption)
end
