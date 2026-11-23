module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.TwQLat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle157
import Formalism.LocalToGlobal.Columns.Bundle017
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle171
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.memberLevelPrime_not_under_twistPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | (intros; apply GlobalTheory.Mem.Col2.ChEx.T_notMem_qv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)}



theorem mem_iff_read (H : I.Reads u I.mu0 j chOf Lb U chi y st k) (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j))
    (hx : x ∈ UAd B.sp.cm (B.R.N j)) :
    x ∈ U (chOf c) ↔ ∃ (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c) := by
  constructor
  · intro hxU
    obtain ⟨q, hq⟩ := OneLevel.pt_exists I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) hx
    obtain ⟨κ, h1, h2, h3⟩ := (H.lev c x q hq).1 hxU
    subst h2
    obtain ⟨γ, h, θ⟩ := κ
    obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
    obtain ⟨hJ, hr⟩ := OneLevel.pt_read I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) h.1 θ.1 hq
    obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
    refine ⟨hJ, hr ▸ h.2, ?_⟩
    have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
    rw [e]
    exact h3
  · rintro ⟨hJ, hm, hc⟩
    exact OneLevel.mem_of_read H c x hJ hm hc

end Read

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem put_mem_J0 (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) : rll_put n v x ∈ J0 hc n ST := by
  have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
  rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
  exact Subgroup.one_mem _

theorem red_put_off (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST)
    (w : SG) (hw : ¬ IsOver v w.1) : redG hc n ST SG ⟨rll_put n v x, hJ⟩ w = 1 :=
  rll_put_red n v x (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 hw

theorem red_put_at {gp : Fin 2 → ℕ} (G : GLoc F E hc.sig gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal)
    (w : SG) (e : (𝓞 E ⧸ w.1.asIdeal) ≃+* kv F v)
    (hcomp : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST) :
    ((redG hc n ST SG ⟨rll_put n v x, hJ⟩ w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).map e =
      redM F v (G.mat a v h 1 x) := by
  have hcomp' : ∀ (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z) := hcomp
  have hw := GlobalTheory.Mem.LevStd.gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have hgE := GlobalTheory.Mem.LevStd.gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
  have hG : G.mat a v h 1 x = ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) (rll_put n v x)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [rll_put_self]; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
  rw [hG, ← h1]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hgE]
  rfl

end Put

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def cvec (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) : Fin (R.N j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  redV P.1 ((qOf P.1 : X.E) • Classical.epsilon fun z => z ∈ cosetIn p P)

end Coset

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Fix

variable {K L : Type} [CommRing K] [CommRing L] {n : ℕ}

theorem fix_inv_iff (M : GL (Fin n) K) (c : Fin n → K) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c ↔ (M : Matrix (Fin n) (Fin n) K) *ᵥ c = c := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fix_map_iff (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    M.map e *ᵥ (fun i => e (c i)) = (fun i => e (c i)) ↔ M *ᵥ c = c := by
  have h : M.map e *ᵥ (fun i => e (c i)) = fun i => e ((M *ᵥ c) i) := by
    have := RingHom.map_mulVec (e : K →+* L) M c
    funext i
    exact (this i).symm
  rw [h]
  constructor
  · intro h'
    funext i
    exact e.injective (congrFun h' i)
  · intro h'
    rw [h']

end Fix

end GlobalTheory.Mem.Col2.TypeRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.MtIndep

section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoRep_trans {W₁ W₂ W₃ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] {S₁ : Submodule ℂ (GAf L n → W₁)} {S₂ : Submodule ℂ (GAf L n → W₂)}
    {S₃ : Submodule ℂ (GAf L n → W₃)} (h₁ : NG.IsoRep S₁ S₂) (h₂ : NG.IsoRep S₂ S₃) : NG.IsoRep S₁ S₃ := by
  obtain ⟨T, hT⟩ := h₁
  obtain ⟨U, hU⟩ := h₂
  exact ⟨T.trans U, fun h f f' e => hU h (T f) (T f') (hT h f f' e)⟩

theorem isoRep_symm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GQ L n) W} {S₁ : Submodule ℂ (GAf L n → W)} {S₂ : Submodule ℂ (GAf L n → W')}
    (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) : NG.IsoRep S₂ S₁ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun h g g' e => ?_⟩
  have hm : NG.rt L n h ((T.symm g : S₁) : GAf L n → W) ∈ S₁ := hs.stable h _ (T.symm g).2
  have key := hT h (T.symm g) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply] at key
  have hg : T ⟨_, hm⟩ = g' := Subtype.ext (key.trans e.symm)
  rw [← hg, LinearEquiv.symm_apply_apply]

theorem isoTyp_eq {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {S₁ S₂ : Submodule ℂ (GAf L n → W)} (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) :
    NG.isoTyp ρ S₁ = NG.isoTyp ρ S₂ := by
  unfold NG.isoTyp
  congr 1
  ext S'
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h' => isoRep_trans (isoRep_symm hs h) h', fun h' => isoRep_trans h h'⟩

end rep

section loc
variable {D : D7}

def BCd (X : LocNd (lay0 D)) (Y : LocAut X) (Pa : List (Part Y.naut.CG)) (loc : ∀ w, Y.naut.LP w)
    (sat : PlE D.host → Multiset ℂ) (inf : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ Y.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, Y.naut.CG a), p.d)).Nodup ∧
  rankIso X.nd Y.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc X.nd Y.naut Pa w = loc w) ∧
  (∀ w, ¬ IsSplitPl D.host w → Y.naut.unr (isoLoc X.nd Y.naut Pa w) ∧
    Y.naut.frobEig (isoLoc X.nd Y.naut Pa w) = ubc D.R.nV (sat w)) ∧
  ∀ τ, isoInf X.nd Y.naut Pa τ = inf τ

def Good (X : LocNd (lay0 D)) (Y : LocAut X) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (j : ℕ) (u : D.nbc.AU j) : Prop :=
  ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧
    BCd X Y (twistIso X.nd Y.naut (Sig ++ [⟨1, c, D.R.t⟩]) Y.naut.etaTinv) (fun w => D.nbc.locAU j u w)
      (D.nbc.satAU j u) (D.nbc.infW j (D.nbc.wtAU j u))

end loc

end GlobalTheory.HeightCounting.MtIndep

namespace GlobalTheory.HeightCounting.MtIndep

section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}

end loc2

end GlobalTheory.HeightCounting.MtIndep
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

section Small
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem row_small_of_mul_eq_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (l : Fin n) (M N : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hMN : M * N = 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) (hM : ∀ j, j ≠ l → Valued.v (M l j) < 1)
    (hl : Valued.v (M l l) = 1) (j : Fin n) (hj : j ≠ l) : Valued.v (N l j) < 1 := by
  have e := congrFun (congrFun hMN l) j
  rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hj), ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at e
  have e2 : M l l * N l j = -∑ i ∈ Finset.univ.erase l, M l i * N i j := eq_neg_of_add_eq_zero_left e
  have h3 : Valued.v (∑ i ∈ Finset.univ.erase l, M l i * N i j) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i hi => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hN i j)) (hM i (Finset.ne_of_mem_erase hi))
  have h4 := congrArg Valued.v e2
  rw [Valuation.map_neg, map_mul, hl, one_mul] at h4
  rw [h4]
  exact h3

theorem val_eq_one_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c)
    (hc : c ≠ 0) : Valued.v z = 1 := by
  obtain ⟨r, rfl, hr⟩ := h
  have hr0 : r ∉ P.asIdeal := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hr0
  have e : z = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) +
      (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hr), ha]

theorem prV_sigR_eq (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul a b => simp [prV, sigR]

variable [StarRing E]

theorem bc_prV_mem_UPts (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (AfE F E)}
    (hk : k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := by
  have hg' : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR_eq]
  have hJ : ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [Matrix.one_apply]
  rw [h1, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Small

theorem map_conj_levStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E)) (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (E ⊗[F] v.adicCompletion F)), k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → k ∈ stabGL (baseDualV hc n ST v) → k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj k).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST v k hU h1 h2 h3
  have key : ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) →
      g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → g ∈ stabGL (baseDualV hc n ST v) →
      g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) →
      ∀ x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v),
      g * x * g⁻¹ ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
    intro g gU gL gD gK x hx
    have hgl : g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := Subgroup.mem_inf.2 ⟨gU, gL⟩
    obtain ⟨hxl, hxD, hxf⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgl hxl) (inv_mem hgl), ⟨mul_mem (mul_mem gD hxD) (inv_mem gD), fun y => ?_⟩⟩
    have hz : ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) ∈
        baseDualV hc n ST v := ((inv_mem gD : g⁻¹ ∈ stabGL (baseDualV hc n ST v)) _).1 y.2
    have h4 := hxf ⟨_, hz⟩
    simp only [fLoc, Submodule.mkQ_apply] at h4 ⊢
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h4 ⊢
    simp only [Submodule.coe_subtype, Submodule.coe_sub] at h4 ⊢
    have e : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) -
        (y : Fin n → E ⊗[F] v.adicCompletion F) =
        (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) -
          ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) := by
      have e1 : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F)) = (y : Fin n → E ⊗[F] v.adicCompletion F) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) =
          (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F))) := by
        simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Matrix.mulVec_sub, e2, e1]
    rw [e]
    exact (gK _).1 h4
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key k hU h1 h2 h3 x hx
  · intro x hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := key k⁻¹ (inv_mem hU) (inv_mem h1) (inv_mem h2) (inv_mem h3) x hx
      rwa [inv_inv] at this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group



theorem basePt_facts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG (E := E) (ST := ST)), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST π hB k c ⟨p₀, hk, hk0⟩ hrow
  classical
  have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hU : k ∈ UAd hc n := hk.uni
  have hkc := hk.lat
  rw [hk0] at hkc
  have hsingle : ∀ j, (Pi.single j 1 : Fin n → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := fun j => by
    refine (mem_latS_std _).2 fun i => ?_
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hInv : ∀ i j, ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have := (mem_latS_std _).1 ((hkc _).1 (hsingle j)) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hK : ∀ i j, ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have h1 : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((k : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hsingle j
      have := (mem_latS_std _).1 ((hkc _).2 h1) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hvI : ∀ (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E), y ∈ Formalism.L2.Herm.intAf F E → Valued.v (adAt F P y) ≤ 1 :=
    fun P y hy => (mem_rInt_iff F E y).1 hy P
  have hsm : ∀ P ∈ ST, ∀ j, j ≠ lastIdx n →
      Valued.v (adAt F P ((k : Matrix (Fin n) (Fin n) (AfE F E)) (lastIdx n) j)) < 1 := by
    intro P hP j hj
    have hr := fun j' => hrow ⟨P, hP⟩ (lastIdx n) j' hl
    refine row_small_of_mul_eq_one (lastIdx n) (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P))
      ((k : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)) ?_ (fun i j => hvI P _ (hK i j)) (fun j' hj' => ?_) ?_ j hj
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := hr j'
      rw [if_neg hj'] at this
      exact DilPt.hasRes_lt_one this
    · have h5 := hr (lastIdx n)
      rw [if_pos rfl] at h5
      have := P.isPrime
      exact val_eq_one_of_hasRes h5 (Units.ne_zero _)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧
      bc (prV (E := E) v) k ∈ stabGL (baseDualV hc n ST v) ∧
      bc (prV (E := E) v) k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
    intro v
    refine GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices hc n hB v _ (bc_prV_mem_UPts hc v hU)
      ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hK i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hK _ j) (fun P hP => hsm P hP j hj)⟩ ?_
    rw [← map_inv]
    refine ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hInv i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hInv _ j) (fun P hP => ?_)⟩
    have := hrow ⟨P, hP⟩ (lastIdx n) j hl
    rw [if_neg hj] at this
    exact DilPt.hasRes_lt_one this
  refine ⟨hU, fun v => ⟨bc_prV_mem_UPts hc v hU, (hloc v).1⟩, fun x => ?_,
    fun v _ => map_conj_levStab hc n ST v _ (bc_prV_mem_UPts hc v hU) (hloc v).1 (hloc v).2.1 (hloc v).2.2⟩
  rw [GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST), GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST)]
  refine forall_congr' fun v => ?_
  have e : (fun i => prV (E := E) v ((k.1 *ᵥ x) i)) =
      ((bc (prV (E := E) v) k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => prV (E := E) v (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [e]
  exact ((hloc v).1 _).symm

end GlobalTheory.Mem.Col2.ChEx
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitLocalLevel_firstFactor_reads_component : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  first | exact @GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | exact GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt | (intros; apply GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


theorem _root_.GlobalTheory.T.rowsLifts_heckeOperators_commute : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  first | exact @GlobalTheory.Mem.R3.Comm.rows_lifts_comm | exact GlobalTheory.Mem.R3.Comm.rows_lifts_comm | (intros; apply GlobalTheory.Mem.R3.Comm.rows_lifts_comm <;> assumption)
end
