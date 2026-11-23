module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle401
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle406
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_framedLevel_iff_two_adelic_points : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  exact @GlobalTheory.Mem.Col2.TopCh.mem_topU_iff
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι)
    (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ (n : ℕ) (t s : GA B n) (θ : GLQ B.fields.E n (I.Q a)),
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
      bc (prV (E := B.host.E) v) t = 1) →
    (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
    (LocCQ (I.Q a) n (t⁻¹ * s * t) θ ↔ θ = 1) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.locCQ_conj_iff_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localMove_classRep_iff_localConditions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m →
    ∀ (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1),
    LocMv I u a i c s κ ↔ ((I.stp u a i).gam c.1 κ = 1 ∧
      cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
      LocalCondMoveDecoratedLattice u (B.R.N i) s κ.2.1.1 ∧ LocCQ (I.Q a) (B.R.N i) s κ.2.2.1) := by
  exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section CosetFixAux

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem redV_qsmul_of_mem {v : Sp E n} (hv : v ∈ stdAt E n P) : redV P (((qOf P : ℕ) : E) • v) = 0 := by
  funext i
  show redP P (((qOf P : ℕ) : E) * v i) = 0
  rw [reduction_mul (GlobalTheory.TopStep.intAt_nat _) (GlobalTheory.TopStep.mem_stdAt.1 hv i), GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_mul]

theorem mem_stdAt_iff_redV_qsmul (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {v : Sp E n}
    (hv : ((qOf P : ℕ) : E) • v ∈ stdAt E n P) : v ∈ stdAt E n P ↔ redV P (((qOf P : ℕ) : E) • v) = 0 := by
  refine ⟨redV_qsmul_of_mem, fun h => GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_⟩
  have hi : IntAt P (((qOf P : ℕ) : E) * v i) := GlobalTheory.TopStep.mem_stdAt.1 hv i
  have h0 : redP P (((qOf P : ℕ) : E) * v i) = 0 := congrFun h i
  have := GlobalTheory.TopStep.intAt_div_of_redP hq hi h0
  rwa [mul_div_cancel_left₀ _ (GlobalTheory.TopStep.qOf_ne_zero (P := P))] at this

theorem redV_sub_of_mem {v w : Sp E n} (hv : v ∈ stdAt E n P) (hw : w ∈ stdAt E n P) :
    redV P (v - w) = redV P v - redV P w := by
  funext i
  exact GlobalTheory.TopStep.reduction_sub (GlobalTheory.TopStep.mem_stdAt.1 hv i) (GlobalTheory.TopStep.mem_stdAt.1 hw i)

theorem redV_qsmul_eq {a b : Sp E n} (hba : b - a ∈ stdAt E n P) (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) :
    redV P (((qOf P : ℕ) : E) • b) = redV P (((qOf P : ℕ) : E) • a) := by
  have hd : ((qOf P : ℕ) : E) • (b - a) ∈ stdAt E n P := by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hba _
  have hb : ((qOf P : ℕ) : E) • b ∈ stdAt E n P := by
    have := add_mem hd ha
    rwa [← smul_add, sub_add_cancel] at this
  have h1 := redV_sub_of_mem hb ha
  rw [← smul_sub, redV_qsmul_of_mem hba] at h1
  exact (sub_eq_zero.1 h1.symm)

end CosetFixAux

theorem setOf_sub_mem_eq_iff {V : Type} [AddCommGroup V] {A : Type} [Ring A] [Module A V] (M : Submodule A V) (a b : V) :
    {z | z - b ∈ M} = {z | z - a ∈ M} ↔ b - a ∈ M := by
  constructor
  · intro h
    have hb : b ∈ {z | z - b ∈ M} := by simp
    rw [h] at hb
    exact hb
  · intro h
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz
      have := add_mem hz h
      rwa [sub_add_sub_cancel] at this
    · intro hz
      have := sub_mem hz h
      rwa [sub_sub_sub_cancel_right] at this

section CosetFix



theorem cosetIn_smul_eq_iff : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  intro X Pr R sel S mu cst u j hj p p' h h1 h2 P hP hdu
  classical
  obtain ⟨y, hy, hY⟩ := p.mem_ybSet hj
  have hyP : ((qOf P.1 : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := (Submodule.mem_iInf _).1 hy P
    simpa [Submodule.mem_comap, hP] using this
  have hN : p'.1.1.deco.1.N = p.1.1.deco.1.N := by
    rw [h1]
    exact Submodule.map_id _
  have hY' : p'.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) p'.1.1.deco.1.N
      fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)} := by
    rw [h2, hN]
    exact hY
  have hc := GlobalTheory.BaseCosetPt.cosetIn_eq_of p P hP y _ (by simp [hP]) hY
  have hc' := GlobalTheory.BaseCosetPt.cosetIn_eq_of p' P hP y _ (by simp [hP]) hY'
  set w : Pr.vGs := ⟨P.1, hP⟩ with hw
  have hf : GlobalTheory.TopStep.IsLiftFr p.1.1.deco.1 w (frsF sel mu p.1.1 P) := by
    unfold frsF
    rw [dite_eq_left hP]
    exact GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
  have key : ∀ q : ChPt (R := R) sel mu u j,
      q = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 →
      GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (q.deco.1.liftFr w) := by
    intro q hq
    have := GlobalTheory.TopStep.liftFr_spec q.deco.2 w
    subst hq
    exact this
  have hf' : GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (frsF sel mu p'.1.1 P) := by
    unfold frsF
    rw [dite_eq_left hP]
    exact key _ h1
  set κ := GlobalTheory.TopStep.passFr 1 h hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL _ P.1 κ = h w := GlobalTheory.TopStep.redGL_passFr 1 h hf hf'
  set a := (frsF sel mu p.1.1 P).symm y with ha
  have hκa : κ.1 a = (frsF sel mu p'.1.1 P).symm y := by
    change (frsF sel mu p'.1.1 P).symm ((frsF sel mu p.1.1 P) a) = _
    rw [ha, LinearEquiv.apply_symm_apply]
  have hqa : ((qOf P.1 : ℕ) : X.E) • a ∈ stdAt X.E (R.N j) P.1 := by
    rw [ha, ← map_smul]
    exact GlobalTheory.BaseCosetPt.frsF_symm_mem p.1.1 P hyP
  have hqd : ((qOf P.1 : ℕ) : X.E) • (κ.1 a - a) ∈ stdAt X.E (R.N j) P.1 := by
    rw [smul_sub, ← map_smul]
    exact sub_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa
  have hcv : cvec p P = redV P.1 (((qOf P.1 : ℕ) : X.E) • a) := by
    unfold cvec
    have hm : ∃ z, z ∈ cosetIn p P := ⟨a, by rw [hc]; simp⟩
    have hε := Classical.epsilon_spec (p := fun z => z ∈ cosetIn p P) hm
    generalize Classical.epsilon (fun z => z ∈ cosetIn p P) = ε at hε ⊢
    rw [hc] at hε
    exact redV_qsmul_eq hε hqa
  rw [hc, hc', ← hκa, setOf_sub_mem_eq_iff, mem_stdAt_iff_redV_qsmul hdu.2 hqd, smul_sub, ← map_smul,
    redV_sub_of_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa, GlobalTheory.TopStep.redV_redGL κ hqa, hred, sub_eq_zero, hcv]

end CosetFix

end GlobalTheory.Mem.Col2.TypeRead
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AutModel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def compE (e : W ≃ₗ[ℂ] W') : (GAf L n → W) ≃ₗ[ℂ] (GAf L n → W') :=
  LinearEquiv.piCongrRight fun _ => e

theorem compE_symm (e : W ≃ₗ[ℂ] W') : compE (L := L) (n := n) e.symm = (compE e).symm :=
  LinearEquiv.ext fun _ => rfl

theorem rt_compE (e : W ≃ₗ[ℂ] W') (h : GAf L n) (f : GAf L n → W) :
    NG.rt L n h (compE e f) = compE e (NG.rt L n h f) := rfl

def conjRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem conjRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') :
    conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

theorem conjRep_inter (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W) :
    e (ρ γ x) = conjRep e ρ γ (e x) := by simp [conjRep_apply]

theorem isSubrep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S) :
    NG.IsSubrep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨h1, N, hN, h2⟩ := hS.le hf
    refine ⟨fun γ g => ?_, N, hN, fun κ hκ g => ?_⟩
    · change e (f (γ * g)) = ρ' γ (e (f g))
      rw [h1 γ g, he]
    · change e (f (g * κ)) = e (f g)
      rw [h2 κ hκ g]
  · rintro h _ ⟨f, hf, rfl⟩
    exact ⟨NG.rt L n h f, hS.stable h f hf, rfl⟩

theorem isIrrRep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) :
    NG.IsIrrRep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  have he' : ∀ γ y, e.symm (ρ' γ y) = ρ γ (e.symm y) := fun γ y => by
    apply e.injective; rw [he]; simp
  obtain ⟨hsub, hne, hmin⟩ := hS
  refine ⟨isSubrep_map e he hsub, ?_, fun S' hS' hle => ?_⟩
  · intro h0
    apply hne
    have := congrArg (Submodule.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) h0
    rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (compE (L := L) (n := n) e).injective] at this
  · set T := S'.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) with hT
    have hTm : T = S'.map (compE (L := L) (n := n) e.symm : (GAf L n → W') →ₗ[ℂ] (GAf L n → W)) := by
      rw [compE_symm, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    have hTs : NG.IsSubrep ρ T := hTm ▸ isSubrep_map e.symm he' hS'
    have hTle : T ≤ S := by
      have := Submodule.comap_mono (f := (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) hle
      rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective] at this
    have hS'eq : S' = T.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) := by
      rw [hT, Submodule.map_comap_eq_of_surjective (compE (L := L) (n := n) e).surjective]
    rcases hmin T hTs hTle with h | h
    · left; rw [hS'eq, h, Submodule.map_bot]
    · right; rw [hS'eq, h]

theorem isoRep_map (e : W ≃ₗ[ℂ] W') (S : Submodule ℂ (GAf L n → W)) :
    NG.IsoRep S (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨(compE e).submoduleMap S, fun h f f' hf => ?_⟩
  simp only [LinearEquiv.submoduleMap_apply]
  rw [hf, rt_compE]

omit [Field L] [NumberField L] [IsCMField L] in
theorem irr_iff {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SubrepTopBot.main
  | exact _root_.GlobalTheory.SubrepTopBot.main
  | (apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubrepTopBot.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubrepTopBot.main ..)

theorem irr_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : ρ.IsIrreducible) :
    (conjRep e ρ).IsIrreducible := by
  rw [irr_iff] at h ⊢
  obtain ⟨hW, hmin⟩ := h
  refine ⟨e.symm.surjective.nontrivial, fun U' hU' => ?_⟩
  have hU : ∀ γ, ∀ x ∈ U'.comap (e : W →ₗ[ℂ] W'), ρ γ x ∈ U'.comap (e : W →ₗ[ℂ] W') := by
    intro γ x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [conjRep_inter]; exact hU' γ _ hx
  have hback : U' = (U'.comap (e : W →ₗ[ℂ] W')).map (e : W →ₗ[ℂ] W') :=
    (Submodule.map_comap_eq_of_surjective e.surjective U').symm
  rcases hmin _ hU with h0 | h0
  · left; rw [hback, h0, Submodule.map_bot]
  · right; rw [hback, h0, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

theorem alg_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : IsAlgWeight L n ρ)
    [FiniteDimensional ℂ W'] : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨-, ι, hι, hd, b, P, hP⟩ := h
  refine ⟨inferInstance, ι, hι, hd, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

theorem exists_autRepM (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) :
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  let e : π.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ π.W) → ℂ) := (Module.finBasis ℂ π.W).equivFun
  let m : GlobalTheory.AutQuot.AutRepM L n :=
    { d := Module.finrank ℂ π.W
      ρ := conjRep e π.ρ
      alg := alg_conj e π.alg
      irr := irr_conj e π.irr
      S := π.S.map (compE (L := L) (n := n) e : (GAf L n → π.W) →ₗ[ℂ] (GAf L n → _))
      irrS := isIrrRep_map e (conjRep_inter e π.ρ) π.irrS }
  exact ⟨m, ⟨e, conjRep_inter e π.ρ⟩, isoRep_map e π.S⟩

end GlobalTheory.AutModel

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Cut

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}

def frStab (P : HeightOneSpectrum (𝓞 E)) (C : Set (Sp E n)) : Subgroup ↥(GLint E n P) where
  carrier := {g | ∀ v, g.1 v ∈ C ↔ v ∈ C}
  one_mem' _ := Iff.rfl
  mul_mem' {a b} ha hb v := (ha (b.1 v)).trans (hb v)
  inv_mem' {a} ha v := by
    have h := ha ((a⁻¹).1 v)
    have e : a.1 ((a⁻¹).1 v) = v := LinearEquiv.apply_symm_apply a.1 v
    rw [e] at h
    exact h.symm

theorem mem_frStab {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} {g : ↥(GLint E n P)} :
    g ∈ frStab P C ↔ ∀ v, g.1 v ∈ C ↔ v ∈ C := Iff.rfl

def cutQ (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : LevQFam E K n Q := fun P =>
  ⟨(Θ P).H ⊓ frStab P.1 (C P), (Θ P).lam.comp (Subgroup.inclusion inf_le_left)⟩

theorem mem_cutQ_grp {Θ : LevQFam E K n Q} {C : ∀ P : Q, Set (Sp E n)} {t : GLQ E n Q} :
    t ∈ (cutQ Θ C).grp ↔ t ∈ Θ.grp ∧ ∀ P, t P ∈ frStab P.1 (C P) := by
  simp only [LevQFam.grp, Subgroup.mem_pi, Set.mem_univ, forall_const]
  exact forall_and

theorem cutQ_grp_le (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : (cutQ Θ C).grp ≤ Θ.grp := fun _ ht => (mem_cutQ_grp.1 ht).1

end Cut

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
def cqOf (q : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) : Set (Sp X.E (R.N j)) :=
  cosetIn q ⟨P.1, Finset.mem_union_right _ P.2⟩

end Pt

end GlobalTheory.Mem.Col2.ChEx

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Inv

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

def InvActs (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (r : PtY ST SG Q y) (P : Q),
    cq (ya Λ Θ g r) P = (fun v => (g.2.2.1 P).1 v) '' cq r P

def PtDet (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ r r' : PtY ST SG Q y, r.1.1 = r'.1.1 → bar r = bar r' → cq r = cq r' → r = r'

end Inv

theorem mem_map_conj {G : Type} [Group G] (S : Subgroup G) (k x : G) :
    x ∈ S.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ S := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨k⁻¹ * x * k, h, by simp [mul_assoc]⟩

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) (i : ℕ) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev lvQ (a : I.ι) (i : ℕ) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev rpT (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : PtAt B.R I.sel (I.tup a) (I.cst a) u i :=
  rp (lvG I a i) (lvQ I a i) ((I.Tp a).pref u i) (I.pref u a i) c

open Classical in
theorem q_sub_SQ (a : I.ι) : I.Q a ⊆ I.SQ := by
  intro P hP
  unfold ColIn.SQ
  exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hP⟩

theorem q_disj (hI : I.Ok) (a : I.ι) : ∀ P ∈ QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K), P ∉ (B.primes X).vGs := by
  intro P hP hG
  exact Finset.disjoint_left.1 (LevTwist.levOk_twists B X I hI).2.1 hG (q_sub_SQ I a hP)

theorem q_conj (hI : I.Ok) (a : I.ι) : ∀ P : I.Q a, conjPrime₂ P.1 ≠ P.1 := by
  intro P hc
  obtain ⟨-, hs⟩ := (LevTwist.levOk_twists B X I hI).1
  have hm : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp [uSG, q_sub_SQ I a P.2]
  exact hs _ hm (by rw [hc]; exact hm)

theorem cos_of_neT {u : B.Word} {a : I.ι} {i : ℕ} (h : i + 1 ≠ B.R.m) (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u i) :
    cosetIn q = cosetIn q' := by
  have e : ∀ r : PtAt B.R I.sel (I.tup a) (I.cst a) u i, r.1.2 = ∅ := fun r => by
    have hr := r.2
    rw [ysAt_ys_of_ne (h := h)] at hr
    exact Set.mem_singleton_iff.1 hr
  funext P
  ext z
  simp [cosetIn, e q, e q']

end Main

end GlobalTheory.Mem.Col2.ChEx
end
end
end

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.leadingMinor_blockDecomposition : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  first | exact @GlobalTheory.FlagFibre.lminor_block | exact GlobalTheory.FlagFibre.lminor_block | (intros; apply GlobalTheory.FlagFibre.lminor_block <;> assumption)
end
