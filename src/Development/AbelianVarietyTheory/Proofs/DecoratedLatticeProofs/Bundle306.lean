module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

@[expose] public section

section

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont.LevelConj

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


omit [NumberField E] in
theorem exists_proj_eq (x : ∀ v, GLoc σ J v) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ g : GAd σ J, (∀ v ∈ S, proj σ J v g = x v) ∧ (∀ v ∉ S, proj σ J v g = 1) ∧ ∀ w, projArch σ J w g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨emb σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [proj_emb_self, h2 v hu, mul_one]
      · rw [proj_emb_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, projArch_emb, one_mul, h3]


omit [NumberField E] in
theorem exists_projArch_eq (x : ∀ w, GArch σ J w) (S : Finset (InfinitePlace F)) :
    ∃ g : GAd σ J, (∀ w ∈ S, projArch σ J w g = x w) ∧ (∀ w ∉ S, projArch σ J w g = 1) ∧ ∀ v, proj σ J v g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨embArch σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [projArch_embArch_self, h2 v hu, mul_one]
      · rw [projArch_embArch_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, projArch_embArch_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, proj_embArch, one_mul, h3]

private theorem eventually_latLoc_eq_std_of_selfDual {L : Submodule (𝓞 E) (Fin n → E)}
    (hJ : J.det ≠ 0) (hL : Submodule.IsLattice E L) (hdual : ∀ v, IsSelfDualAt σ J L v) :
    ∀ᶠ v in cofinite, latLoc F L v = latLoc F (stdLattice E n) v := by
  have hstd : Submodule.IsFullLattice E (stdLattice E n) := isLattice_stdLattice
  filter_upwards [eventually_latLoc_le (F := F) hL.fg hstd.span_eq_top,
    AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ hstd] with v hle hv
  apply le_antisymm hle
  intro y hy
  rw [hdual v]
  rw [hv] at hy
  exact fun x hx => hy x (hle hx)

omit [NumberField E] in
theorem exists_conj_of_local {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hlat : ∀ᶠ v in cofinite, latLoc F L v = latLoc F L' v)
    (a a' : GL (Fin n) (AF F ⊗[F] E))
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : GLoc σ J v, ∀ k : GLoc σ J v,
      k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v)
    (hi : ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w,
      k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔
        g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) :
    ∃ g : GAd σ J, ∀ k : GAd σ J, k ∈ levelAll σ J L' a' ↔ g⁻¹ * k * g ∈ levelAll σ J L a := by
  choose x hx using hf
  choose y hy using hi
  have hS := Filter.eventually_cofinite.1 hlat
  obtain ⟨g, g1, g2, g3⟩ := exists_proj_eq σ J x hS.toFinset
  obtain ⟨h, h1, -, h3⟩ := exists_projArch_eq σ J y Finset.univ
  refine ⟨g * h, fun k => ?_⟩
  rw [mem_levelAll, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [map_mul, map_mul, map_inv, map_mul, h3, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [g1 v hv]
      exact hx v _
    · have e : latLoc F L v = latLoc F L' v := by simpa using hv
      rw [g2 v hv, inv_one, one_mul, mul_one, mem_stabLoc, mem_stabLoc, e]
  · rw [map_mul, map_mul, map_inv, map_mul, g3, one_mul, h1 w (Finset.mem_univ w)]
    exact hy w _

end Glue

theorem exists_conj : ∀ (D : D7) (T : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a a' : GL (Fin T.rank) (AE D)), IsLevel T L a → IsLevel T L' a' → ∃ g : GA D T, ∀ k : GA D T, k ∈ lev T L' a' ↔ g⁻¹ * k * g ∈ lev T L a := by
  intro D T L L' a a' h h'
  have hc := isCMExt_host D
  have hJ := isHermND_gram T
  have hf := fun v => GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified D.host.F D.host.E D.sp.cm.sig hc (GlobalTheory.HeckeAdjoint.unramified_host D) T.rank T.gram
    hJ L L' h.lat h'.lat v (h.dual v) (h'.dual v)
  have hi := fun w => GlobalTheory.T.archimedean_majorant_stabilisers_conjugate D.host.F D.host.E D.sp.cm.sig hc T.rank T.gram hJ a a' h.maj h'.maj w
  have hlat : ∀ᶠ v in cofinite, latLoc D.host.F L v = latLoc D.host.F L' v := by
    filter_upwards [eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h.lat h.dual,
      eventually_latLoc_eq_std_of_selfDual D.sp.cm.sig T.gram hJ.2 h'.lat h'.dual] with v hv hv'
    exact hv.trans hv'.symm
  obtain ⟨g, hg⟩ := exists_conj_of_local D.sp.cm.sig T.gram hlat a a' hf hi
  exact ⟨g, fun k => hg k⟩

end GlobalTheory.EisCont.LevelConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameAt
variable {D : D7}

theorem mem_congGrp (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  have key : ∀ i j, (Ideal.Quotient.mk I) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  constructor
  · intro h i j
    have := congrArg (fun u : GL (Fin V.rank) (AE D ⧸ I) => u.1 i j) h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one] at this
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key]
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq, key] at this
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
    exact this

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_mul (g h : GA D S) : Formalism.L2.Theta.mt S (g * h) = Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S h := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h1 := p.pr_sec (p.pr 1)
  rw [p.sec_pr, mul_one, map_one] at h1
  exact h1

theorem gl_map (β : Frame p S n) (g : GL n k) :
    (Formalism.L2.Theta.mt S (β.gl g)).map p.pr = β.b * g.val * β.b' := β.gl_mat g

theorem gl_inj (β : Frame p S n) : Function.Injective β.gl := by
  intro g g' h
  have h1 := congrArg (fun x => β.b' * (Formalism.L2.Theta.mt S x).map p.pr * β.b) h
  simp only [gl_map] at h1
  have e1 : ∀ x : Matrix n n k, β.b' * (β.b * x * β.b') * β.b = x := by
    intro x
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, β.b'b, Matrix.one_mul, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e1, e1] at h1
  exact Units.ext h1

theorem det_at (β : Frame p S n) (g : GL n k) :
    ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  set a := (Formalism.L2.Theta.mt S (β.gl g)).det
  set c := (Formalism.L2.Theta.mt S (β.gl g⁻¹)).det
  have hee : p.e * p.e = p.e := p.split.1
  have hac : a * c = 1 := by
    simp only [a, c]
    rw [← Matrix.det_mul, ← mt_mul, ← map_mul, mul_inv_cancel, map_one, mt_one, Matrix.det_one]
  refine ⟨⟨p.e * a + (1 - p.e), p.e * c + (1 - p.e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · linear_combination (2 - a - c) * hee + p.e * p.e * hac
  · simp only [Units.val_mk, map_add (f := _), map_mul, map_sub, map_one, pr_e p, one_mul, sub_self, add_zero]
    simp only [a]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, gl_map, Matrix.mul_assoc, Matrix.det_comm' β.bb' β.b'b, Matrix.mul_assoc, β.b'b,
      Matrix.mul_one]
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mem_grpAt_iff (β : Frame p S n) (h : GA D S) : h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hL := (GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1
  unfold grpAt
  rw [mem_congGrp]
  constructor
  · intro hh
    have hsupp : SuppAt p.e S h := by
      intro i j
      rw [hsum]
      exact (hL _).1 (hh i j)
    let M := (Formalism.L2.Theta.mt S h).map p.pr
    let M' := (Formalism.L2.Theta.mt S h⁻¹).map p.pr
    have hMM : M * M' = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM'M : M' * M = 1 := by
      simp only [M, M']
      rw [← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : ∀ X Y : Matrix (Fin S.rank) (Fin S.rank) k,
        β.b' * X * β.b * (β.b' * Y * β.b) = β.b' * (X * Y) * β.b := by
      intro X Y
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
    let g : GL n k := ⟨β.b' * M * β.b, β.b' * M' * β.b, by rw [e2, hMM, Matrix.mul_one, β.b'b],
      by rw [e2, hM'M, Matrix.mul_one, β.b'b]⟩
    refine ⟨g, GlobalTheory.T.eq_of_splitPart_agree_supportedAtSplitPlace D S p.e h (β.gl g) p.split hsupp (β.gl_supp g) ?_⟩
    intro i j
    rw [← p.sec_pr, ← p.sec_pr]
    congr 1
    have := congrArg (fun X => X i j) (gl_map β g)
    simp only [Matrix.map_apply] at this
    rw [this]
    show M i j = (β.b * (β.b' * M * β.b) * β.b') i j
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨g, rfl⟩ i j
    rw [(hL _)]
    have := β.gl_supp g i j
    rw [hsum] at this
    exact this
end

theorem frame_facts : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  intro D k _ _ _ _ p S n _ _ β
  refine ⟨mem_grpAt_iff β, gl_inj β, GlobalTheory.T.continuous_splitPlaceHermitianFrame_GL_embedding D k p S n β, GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β, ?_, det_at β⟩
  intro L Λ hL hΛ
  first
  | exact GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k p S n β L Λ hL hΛ
  | exact GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k p S n β L Λ hL hΛ.toIsLattice

end GlobalTheory.FrameAt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkKapInv

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem isHalf_mul_l {e : AE D} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hx k j]

theorem isHalf_mul_r {e : AE D} {l m n : ℕ} {x : Mx D l m} (hx : IsHalf e x) (A : Mx D m n) : IsHalf e (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx i k]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) :=
  fun i j => by
    show cA D e * cA D (x j i) = cA D (x j i)
    rw [← map_mul, hx j i]

def tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (_l : Link B L' ζ') :
    Matrix (Fin L'.rank) (Fin B.L.rank) D.host.E := fun i j => -(B.ζ j)⁻¹ * ζ' i

theorem mul_tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    l.τ * tauPlus l = 1 := by
  obtain ⟨hr, hq⟩ := B.line
  have hsub : ∀ a b : Fin B.L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hne : ∀ a, B.ζ a ≠ 0 := by
    intro a ha
    apply hq
    have h0 : B.ζ = 0 := funext fun b => by rw [hsub b a]; exact ha
    rw [h0]; simp
  funext a b
  rw [hsub b a, Matrix.one_apply_eq, Matrix.mul_apply]
  have hm := congrFun l.map a
  rw [Pi.neg_apply, Matrix.mulVec, dotProduct] at hm
  simp only [tauPlus]
  calc ∑ k, l.τ a k * (-(B.ζ a)⁻¹ * ζ' k) = -(B.ζ a)⁻¹ * ∑ k, l.τ a k * ζ' k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hm, neg_mul_neg, inv_mul_cancel₀ (hne a)]

theorem kappa_inv : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ')
    (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧
      ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  intro D ρ B L' ζ' l S P h
  refine ⟨(rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h, ?_, fun hh => ?_, fun e he => ?_⟩
  · show ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) * ((rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h)) = h
    rw [← Matrix.mul_assoc, ← rat_mul, mul_tauPlus l, rat_one, Matrix.one_mul, GlobalTheory.LastOpPf.ofAdj_starAdj]
  · exact GlobalTheory.LastOpPf.mxAt_mul_l _ (GlobalTheory.LastOpPf.mxAt_smul _ (GlobalTheory.LastOpPf.mxAt_mul_l _
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LastOpPf.mxAt_adj hh) _)))
  · exact isHalf_mul_l _ (isHalf_smul _ (isHalf_mul_l _ (isHalf_mul_r (isHalf_adj he) _)))

end GlobalTheory.LinkKapInv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.RdBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nat_mul_mem (x : k) : ∃ N : ℕ, 0 < N ∧ (N : k) * x ∈ 𝒪[k] := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  letI := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪[k])
  set Q := Fintype.card (IsLocalRing.ResidueField 𝒪[k])
  have hQ : (Q : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hQ
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪[k]) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have h2 : b ∣ ((Q ^ m : ℕ) : 𝒪[k]) := by
    rw [hu, Units.mul_left_dvd, Nat.cast_pow]
    exact pow_dvd_pow_of_dvd hQ m
  obtain ⟨d, hd⟩ := h2
  refine ⟨Q ^ m, pow_pos Fintype.card_pos m, ?_⟩
  have hb1 : (algebraMap 𝒪[k] k b) ≠ 0 := fun h => hb0 (Subtype.ext h)
  have h3 : ((Q ^ m : ℕ) : k) = algebraMap 𝒪[k] k b * algebraMap 𝒪[k] k d := by
    rw [← map_mul, ← hd, map_natCast]
  have h4 : ((Q ^ m : ℕ) : k) * (algebraMap 𝒪[k] k a / algebraMap 𝒪[k] k b) = ((d * a : 𝒪[k]) : k) := by
    rw [h3]
    change _ = algebraMap 𝒪[k] k (d * a)
    rw [map_mul]
    field_simp
  rw [h4]
  exact (d * a).2

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (f : ι → k) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : k) * f i ∈ 𝒪[k] := by
  classical
  choose n hn hf using fun i => exists_nat_mul_mem (f i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (n i : k), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hf i)

end GlobalTheory.FinPl.RdBound


open GlobalTheory.FinPl.RdBound in
theorem GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u → ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := exists_nat_mul_mem_family (fun x : n × Fin T.rank => β.b' x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := exists_nat_mul_mem_family (fun x : Fin S.rank × n' => α.b x.1 x.2)
  refine ⟨K₁ * M * K₂, Nat.mul_pos (Nat.mul_pos hK₁ hM) hK₂, fun u hu hh i j => ?_⟩
  have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
  have hint : ∀ a b, (M : k) * p.pr (u a b) ∈ 𝒪[k] := fun a b => by
    rw [p.int_iff]
    have h1 : p.sec ((M : k) * p.pr (u a b)) = (M : AE D) * u a b := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, p.sec_pr, hh a b]
    rw [h1]
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, map_natCast]
    exact hden _ hu' a b
  change (_ : k) * (β.b' * Matrix.map u p.pr * α.b) i j ∈ 𝒪[k]
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine sum_mem fun a _ => ?_
  have e : ((K₁ * M * K₂ : ℕ) : k) * (β.b' i a * Matrix.map u p.pr a b * α.b b j) =
      ((K₁ : k) * β.b' i a) * ((M : k) * p.pr (u a b)) * ((K₂ : k) * α.b b j) := by
    rw [Matrix.map_apply]; push_cast; ring
  rw [e]
  exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem tailRd_of_clsT : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  intro D c t ρ A hA hcP n h ψ hψ ψ' hψ' a H F
  have e1 := hA.tail n h ψ hψ F
  have e2 := hA.tail n h ψ' hψ' F
  have key : ∀ β (x : A.cl), A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
      a * A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
    intro β x
    have : (fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
        a • (fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
      funext z
      rw [H β ((ρ.fr n).symm z)]
      rfl
    rw [this, map_smul, map_smul, smul_eq_mul]
  simp_rw [key] at e1
  have e3 : t.cP * t.tail n h ψ F = t.cP * (a * t.tail n h ψ' F) := by
    rw [← e1, mul_left_comm t.cP a, ← e2]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  exact mul_left_cancel₀ hcP e3

end GlobalTheory.SeeSaw

end
end
