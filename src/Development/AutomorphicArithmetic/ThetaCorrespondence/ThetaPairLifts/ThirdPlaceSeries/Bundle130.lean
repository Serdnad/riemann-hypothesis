module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle368
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle232
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle475
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448

@[expose] public section

section



section
noncomputable section
section Col
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct
namespace GlobalTheory.FamTraceChiCol.ColRead
end GlobalTheory.FamTraceChiCol.ColRead
end Col
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTraceChiCol.ColRead
open GlobalTheory.SymBridge GlobalTheory.RootEx
theorem colLam_read_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → ∃ (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) ∧ valuation (a.G i).k ((∑ p : Fin (I.rec7 l Z).R.k, ∑ q : Fin (I.rec7 l Z).R.k, if q.val = p.val + 1 then g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q)) else 0) - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1 ∧ GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ κ _ y hκy hy i g hg
  obtain ⟨hS⟩ := hA.tr.std
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨k₀, hR⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hPP : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  obtain ⟨A, -, hA'⟩ := GlobalTheory.FamTrace.TraceFwd.exists_red I hA.tr.ok
    ((TC.spaces_in_coordinates I hA.tr.ok hP l Z).2.2.2 0 (Nat.zero_le _)).1
    ((W.R.T.cols.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev hR ⟨_, hy⟩ (a.pl i).1 hPP
  letI := (a.G i).fld; letI := (a.G i).val; letI := (a.G i).top; letI := (a.G i).loc
  obtain ⟨z, hz, hz'⟩ := exists_close (a.G i).q ((ha.tie row col).2.idem i).1 ((I.rec7 l Z).sp.X 0)
    (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (show B.R.N 0 = B.R.k by simp [Ranks.N]) _
    ((ha.stdG i).1 0 (Nat.zero_le _)) hκy hA' g hg
  obtain ⟨j, hj⟩ := TC.GLev0.mem_vGs.1 hPP
  have h := TC.GLev0.g_mem_under hj
  obtain ⟨w, hw, ρ, hwu, hres⟩ := TC.GLev0.exists_w (X := X) (_root_.GlobalTheory.MiTop.formsAtZero W u).gl (hS u).gl.piG j _ h
  have hwP : w = (a.pl i).1 := TC.GLev0.vGs_inj (X := X) hPP (TC.GLev0.mem_vGs.2 ⟨j, hw⟩) hwu
  subst hwP
  obtain ⟨w', h1, h2⟩ := lamJ_eq (_root_.GlobalTheory.MiTop.formsAtZero W u).gl j h ρ hres hA' ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.chiB j _ h) B.R.k B.R.t z hz
    ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr j _ h) ((hS u).fr0 j _ h)
  exact ⟨j, h, z, w', h1, hz', (GlobalTheory.FamTraceChiCol.colLam_eq (_root_.GlobalTheory.MiTop.formsAtZero W u) j h _).trans h2⟩
end GlobalTheory.FamTraceChiCol.ColRead
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChiCol

theorem trace_chi_col_factor_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (y : (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U), (((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.chi y : ℂˣ) : ℂ) * ∏ i : Fin a.n, GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) y.1 = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a y
  have hTP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := hA.lev.1
  set w : Fin a.n → IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := fun i => (a.pl i).1.under (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) with hw
  have hw_mem : ∀ i, (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ (w i).asIdeal := by
    intro i
    have h1 := hTP.1 (a.pl i).1 (a.pl i).2
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact h1
  have hw_inj : Function.Injective w := by
    intro i i' hii
    obtain ⟨PP, _, hu⟩ := hTP.2 (w i) (hw_mem i)
    have e1 := hu (a.pl i).1 ⟨(a.pl i).2, rfl⟩
    have e2 := hu (a.pl i').1 ⟨(a.pl i').2, hii.symm⟩
    exact a.pl.injective (Subtype.ext (e1.trans e2.symm))
  set S : Fin 2 → Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) :=
    fun j => {v | ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal} with hS
  have hrange : S 0 ∪ S 1 = Set.range w := by
    ext v
    simp only [Set.mem_union, hS, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro hv
      have hv' : (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 0 * (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g 1 : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal := (mem_type_prod_iff v).2 (Fin.exists_fin_two.2 hv)
      obtain ⟨PP, ⟨hPP, hPv⟩, _⟩ := hTP.2 v hv'
      exact ⟨a.pl.symm ⟨PP, hPP⟩, by simp [hw, hPv]⟩
    · rintro ⟨i, rfl⟩
      exact Fin.exists_fin_two.1 ((mem_type_prod_iff (w i)).1 (hw_mem i))
  have hfin : ∀ j, (S j).Finite := fun j =>
    (Set.finite_range w).subset (hrange ▸ (by
      rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;> subst hj
      · exact Set.subset_union_left
      · exact Set.subset_union_right))
  have hdisj : Disjoint (S 0) (S 1) := by
    rw [Set.disjoint_left]
    intro v h0 h1
    exact absurd (type_idx_unique (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) h0 h1) (by decide)
  have hinner : ∀ j : Fin 2,
      (∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g j : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal),
        (Formalism.L2.Forms.lamJ ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j v h) ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.chiB j v h) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.t 0 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.k
          (Formalism.L2.Forms.redM (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat j v h ((_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.fr j v h)
            (Formalism.UG.bc (Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v) y.1))))⁻¹) =
      ∏ᶠ v ∈ S j, (colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) v y.1)⁻¹ := by
    intro j
    refine finprod_congr fun v => finprod_congr fun h => ?_
    rw [colLam_eq (_root_.GlobalTheory.MiTop.formsAtZero W u) j h y.1]
  have hchi := (_root_.GlobalTheory.MiTop.formsAtZero W u).glev0.chi_eq y
  rw [Fin.prod_univ_two, hinner 0, hinner 1, ← finprod_mem_union hdisj (hfin 0) (hfin 1), hrange,
    finprod_mem_range hw_inj, finprod_eq_prod_of_fintype] at hchi
  rw [hchi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (colLam_ne_zero (_root_.GlobalTheory.MiTop.formsAtZero W u) _ _)
end GlobalTheory.FamTraceChiCol
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoPlace
end GlobalTheory.XGeoPlace
theorem GlobalTheory.XGeoPlace.exists_index_place_eq_of_readsStd_of_mem : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (PP : Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (_ : MeasurableSpace k) (_ : BorelSpace k) (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP ∧ q.v = PP.under (𝓞 (I.rec7 l Z).host.F) ∧ q.UnitAA ∧ valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u PP hPP
  have hC := hW.pk.bot.hyp.2.2.2.1
  have hnc : ¬ Lev.IsConjPl PP PP := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl (_root_.GlobalTheory.Fam.pk_z W) W.Q.F.lv2 hC.lev hC.grp PP hg PP hg
    · exact (hC.lev.Q_pl t PP ht).2 PP ht
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hnc
  obtain ⟨k, _, _, _, _, q, hqe, hqv, hint, -⟩ := GlobalTheory.LocMod.SplitCompl.exists_place _ PP e he
  obtain ⟨ℓ, hℓ, hℓP, h2q, hd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal ∧
      (B.host.QS * B.host.q).Coprime ℓ ∧ B.host.d.Coprime ℓ := by
    rcases hPP with hg | ⟨t, ht⟩
    · have hgg := hW.lev.1.1 PP hg
      rw [Nat.cast_mul] at hgg
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((B.host.g i : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rcases PP.isPrime.mem_or_mem hgg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hc : (B.host.g i).Coprime (B.host.QS * B.host.q * B.host.d) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.g_cond i, Nat.gcd_one_left]
      refine ⟨B.host.g i, B.host.g_prime i, hi, (hc.coprime_dvd_right ⟨B.host.d, rfl⟩).symm,
        (hc.coprime_dvd_right (Dvd.intro_left _ rfl)).symm⟩
    · have hoff := (hC.lev.Q_off t PP ht).1
      obtain ⟨ℓ, hℓ, hℓP⟩ := GlobalTheory.XGeoPlace.exists_prime_mem_pl PP
      have key : ∀ m : ℕ, m ∣ B.host.QS * B.host.q * B.host.d * (I.rec7 l Z).sp.T → m.Coprime ℓ := fun m hm =>
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdv =>
          hoff (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (hdv.trans hm)) hℓP))
      exact ⟨ℓ, hℓ, hℓP, key _ ⟨B.host.d * (I.rec7 l Z).sp.T, by ring⟩, key _ ⟨B.host.QS * B.host.q * (I.rec7 l Z).sp.T, by ring⟩⟩
  have hv : (ℓ : 𝓞 (I.rec7 l Z).host.F) ∈ q.v.asIdeal := by
    rw [hqv, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
    exact hℓP
  have hcc : (Ideal.absNorm (I.rec7 l Z).host.ccK).Coprime ℓ := by
    show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _
  have hU : q.UnitAA := GlobalTheory.SeeSaw.StdOff.unitAA_of q hℓ hv h2q hd hcc
  have hT : (((B.T u : ℕ)) : 𝓞 (I.rec7 l Z).host.E) ∉ PP.asIdeal := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact Formalism.L2.Col.T_notMem_vGs l.pr u ⟨PP, (hW.lev.2.1 PP).1 hg⟩
    · exact (hC.lev.Q_off t PP ht).2 u
  set π : 𝓞 (I.rec7 l Z).host.E := X.piT u with hπdef
  have hπ : π ∉ PP.asIdeal := fun h => hT (by
    have h2 := PP.asIdeal.mul_mem_left (B.fields.conjO ((B.primes X).piT u)) h
    have h3 : (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) ∈ PP.asIdeal := by
      rw [mul_comm]
      exact h2
    rw [l.pr.piT_norm u] at h3
    exact h3)
  have hπ0 : (π : (I.rec7 l Z).host.E) ≠ 0 := fun h0 => hπ (by
    rw [show π = 0 from RingOfIntegers.coe_injective (by simpa using h0)]
    exact zero_mem _)
  have e1 : (GlobalTheory.XGeoStd.piE I l Z u) = (π : (I.rec7 l Z).host.E) := rfl
  have hin1 := (hint (π : (I.rec7 l Z).host.E)).2 ⟨π, 1, fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hin2 := (hint (π : (I.rec7 l Z).host.E)⁻¹).2 ⟨1, π, hπ, by simp [hπ0]⟩
  have hinv : (GlobalTheory.LocMod.ofSplit q).pr ((π : (I.rec7 l Z).host.E)⁻¹) = ((GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E))⁻¹ := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _ = (((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _)⁻¹
    exact map_inv₀ _ _
  have hne : (GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E) ≠ 0 := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) (π : (I.rec7 l Z).host.E) ≠ 0
    exact (map_ne_zero _).2 hπ0
  rw [hinv] at hin2
  rw [Valuation.mem_integer_iff] at hin1 hin2
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, borel k, @BorelSpace.mk _ _ (borel k) rfl, q, hqe ▸ he, hqv, hU, ?_⟩
  rw [e1]
  rw [map_inv₀] at hin2
  exact le_antisymm hin1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hne))).1 hin2)
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevelUnif
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
section Elem
variable {κ : Type} [CommRing κ] {r : ℕ}
end Elem
section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
end Local
section Levels
variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}
end Levels
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word}
theorem valuation_uniformizer_sub_q_lt (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) {v : VCom f.c} {N : ℕ} (G : Fin N → GLoc v) (pl : Fin N ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hP : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg) (n : Fin N) :
    valuation (G n).k ((((G n).S.ϖ : (G n).kˣ) : (G n).k) - ((Formalism.L2.Col.qOf (pl n).1 : ℕ) : (G n).k)) <
      valuation (G n).k (((G n).S.ϖ : (G n).kˣ) : (G n).k) := by
  have hid : ∀ i, IsIdemAt (G i).q.e (pl i).1 := fun i => (hR.idem i).1
  have hq : ∀ i, ∃ t : (G i).kˣ, IsUnif t ∧ (t : (G i).k) = ((Formalism.L2.Col.qOf (pl i).1 : ℕ) : (G i).k) := fun i => by
    obtain ⟨-, hi, hd⟩ := place_facts (G i).q (hid i)
    obtain ⟨t, h1, h2⟩ := GlobalTheory.WeilCondUnif.isUnif_of (pl i).1 ((G i).q.pr.comp (incA D)) hi hd (norm_notMem_sq (hP.1 _ (pl i).2))
    exact ⟨t, h1, h2.trans (map_natCast _ _)⟩
  choose t ht htq using hq
  choose α hα using fun i => exists_res (G i).q (hid i) (G i).S.cond (G i).S.unif
  choose β hβ using fun i => exists_res (G i).q (hid i) (G i).S.cond (ht i)
  obtain ⟨ψ₀, -, h0, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hrS : D.R.rS = D.R.m / 2 - 1 := rfl
  have hA : ∀ c, ψ₀ (pl n).1 c = β n c := fun c => by
    let i : Fin D.R.r := ⟨0, by omega⟩
    let j : Fin D.R.r := ⟨1, by omega⟩
    have hij : i ≠ j := fun e => zero_ne_one (congrArg Fin.val e)
    have hE : ∀ a : Fin D.R.r, ¬ supEdge a a := fun a h => by unfold supEdge at h; omega
    let x : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hx : x ∈ (P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).H :=
      single_mem _ _ (unipCol_le _ 0 0 (elem_mem_unipCol hij zero_lt_one c 0 0 one_ne_zero))
    obtain ⟨hx', e1⟩ := chi_of_eq h0 x hx
    have e2 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum supEdge (x PP)) := by
      unfold P0 LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    have e3 := W.Q.signs (fun PP => (G (pl.symm PP)).q.e) (fun PP => by
      have := hid (pl.symm PP)
      rwa [pl.apply_symm_apply] at this) ⟨(_root_.GlobalTheory.Fam.pk_z W).eG.symm x, hx'⟩
    have e4 : (((P0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ψ₀).chi ⟨x, hx⟩ : ℂˣ) : ℂ) = _ := (congrArg Units.val e1).symm.trans e3
    rw [e2, ← pl.prod_comp, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) supEdge hE hij rfl] at e4
    rw [e4, ← prod_single pl β supEdge hE hij rfl n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [pl.symm_apply_apply, psiAt_eq (G m).q (G m).char]
    change _ = β m (edgeSum supEdge (x (pl m)))
    rw [edgeSum_eq_supSum, ← Function.surjInv_eq Ideal.Quotient.mk_surjective (Formalism.IndefR.Mi.supSum (x (pl m)).val), ← hβ,
      Units.val_inv_eq_inv_val, htq, MulEquiv.apply_symm_apply]
    refine congrArg (fun y => ((G m).S.ψ y : ℂ)) ?_
    change ((G m).q.pr.comp (incA D)) _ = _
    rw [map_mul, map_inv₀, map_natCast]
    rfl
  have hC : ∀ c, ψ₀ (pl n).1 c = α n c := fun c => by
    let i : Fin D.R.r := ⟨D.R.rS, by omega⟩
    let j : Fin D.R.r := ⟨D.R.rS + 1, by omega⟩
    have hij : i ≠ j := fun e => by have := congrArg Fin.val e; simp [i, j] at this
    have hE : ∀ a : Fin D.R.r, ¬ symEdge D.R.rS D.R.k a a := fun a h => by unfold symEdge at h; omega
    have hEij : symEdge D.R.rS D.R.k i j := Or.inl ⟨rfl, by show D.R.rS + 1 ≠ _; omega, by show D.R.rS + 1 ≠ _; omega⟩
    let y : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := Pi.mulSingle (pl n) (elem hij c)
    have hy : y ∈ (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).H :=
      single_mem _ _ (elem_mem_unipCol hij (Nat.lt_succ_self _) c _ _ (by show D.R.rS + 1 ≠ _; omega))
    let g : G0 (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r := reord π.symm y
    have hgy : ∀ PP a b, (y PP).val a b = (g PP).val (π a) (π b) := fun PP a b => by
      change _ = (y PP).val (π.symm (π a)) (π.symm (π b))
      rw [π.symm_apply_apply, π.symm_apply_apply]
    have hre : reord π g = y := funext fun PP => Units.ext (Matrix.ext fun a b => (hgy PP a b).symm)
    have hg : g ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hH g).2 (hre ▸ hy)
    choose x hx using (hR.lev g).1.1 hg
    have e1 := (hR.lev g).2 hg x hx
    have e2 : (_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g, hg⟩ = (PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ :=
      (hχ g hg (hre ▸ hy)).trans (congrArg _ (Subtype.ext hre))
    have e3 : (((PsharpSym (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r D.R.rS D.R.k ψ₀).chi ⟨y, hy⟩ : ℂˣ) : ℂ) =
        ∏ PP : (_root_.GlobalTheory.Fam.pk_z W).Pg, ψ₀ PP.1 (edgeSum (symEdge D.R.rS D.R.k) (y PP)) := by
      unfold PsharpSym LevelP.ofLocal
      rw [MonoidHom.finsetProd_apply, Units.coe_prod]
      rfl
    rw [← e2, e1, ← pl.prod_comp, prod_single pl (fun m => ψ₀ (pl m).1) _ hE hij hEij, Units.coe_prod] at e3
    rw [← e3, ← prod_single pl α _ hE hij hEij n c]
    refine Finset.prod_congr rfl fun m _ => ?_
    have h1 := (G m).hs
    have h2 := (G m).S.odd
    have hρ : D.R.rS = (G m).S.ρ := by omega
    let e : Fin D.R.k ⊕ Fin ((G m).s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by omega))
    have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
    have := sym_chr (G m).S (prO (G m).q) e he (hρ ▸ hπ) (g (pl m)) (y (pl m)) (hgy _) (α m) (hα m) (x m)
      fun a b => hx m a b _ _ (he a) (he b)
    rw [← hρ] at this
    exact this
  rw [← htq]
  exact near_of_res (G n).q (hid n) (G n).S.cond (G n).S.unif (ht n) fun z =>
    Circle.coe_injective ((hα n z).trans (((hC _).symm.trans (hA _)).trans (hβ n z).symm))
end Gen
theorem int_and_unif_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ n
  have hR := (ha.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g W.Q.stdChar t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  have h2 := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
  exact ⟨(place_facts (a.G n).q (hR.idem n).1).2.1, h2⟩
end GlobalTheory.LevelUnif
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames

theorem exists_locX_std_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX) (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((_root_.GlobalTheory.Fam.pk_z W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (_root_.GlobalTheory.Fam.pk_z W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _
  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]
end GlobalTheory.XGeoStd.Frames
end
end
end
