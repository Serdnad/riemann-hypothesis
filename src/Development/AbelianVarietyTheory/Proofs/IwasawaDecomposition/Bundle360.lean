module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle260
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Formalism.LocalToGlobal.Columns.Bundle015
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df



theorem cols_ipV_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (c : ((I.cols l).mem u).C.cls 0)
    (f g : ((I.cols l).mem u).C.Y 0 → ℂ) :
    ((I.cols l).fm u).ipV 0 c f g = starRingEnd ℂ (((I.cols l).fm u).ipV 0 c g f) :=
  ClassSumPos.ipVal_herm _ _ _ f g

theorem cols_ipC_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word)
    (φ ψ : ((I.cols l).mem u).C.cls 0 → ((I.cols l).mem u).C.Y 0 → ℂ) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 ψ φ) = ((I.cols l).fm u).ipC 0 φ ψ := by
  unfold MemberForms.ipC

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, cols_ipV_herm I l u c (φ c) (ψ c)]
  congr 1
  simp [ColumnChain.wt]

theorem cols_pos : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    SpectralModel.ColsPos (I.cols l) := by
  intro B X I _ _ l _ u
  refine ⟨fun x _ y _ => cols_ipC_herm I l u x y, fun x hx h0 => ?_⟩
  exact ipC_zero_re_pos B (I.cols l) u (fun φ ψ => (cols_ipC_herm I l u ψ.1 φ.1).symm) ⟨x, hx⟩
    (fun h => h0 (congrArg Subtype.val h))

end GlobalTheory.Mem.Df
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

open GlobalTheory.TopStep
open GlobalTheory.Mem.Col2.PtExist (mat)

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_dep_eq_exp (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : ∃ N : ℕ, dep P c = WithZero.exp (-(N : ℤ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, dep P c = WithZero.exp m := ⟨_, (WithZero.exp_log (dep_ne_zero c)).symm⟩
  have h1 : m ≤ 0 := by
    have := dep_le_one (P := P) c
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  refine ⟨(-m).toNat, ?_⟩
  rw [hm, Int.toNat_of_nonneg (by omega), neg_neg]

variable [StarRing E]

theorem sm_of_lqPrinc {P : HeightOneSpectrum (𝓞 E)} {N c : ℕ} (hd : dep P c = WithZero.exp (-(N : ℤ))) {g : Sp E n ≃ₗ[E] Sp E n}
    (h : lqPrinc P N g) : Sm Valued.v (dep P c) (ratM P g - 1) := by
  intro i j
  have e : (ratM P g - 1) i j = algebraMap E (P.adicCompletion E) ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) := by
    have e1 : mat g i j = LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) i j := by
      rw [LinearMap.toMatrix'_apply]
      rfl
    simp only [Matrix.sub_apply, map_sub, ratM, Matrix.map_apply, e1, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, valued_algebraMap, hd]
  exact h i j

end Loc

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TC

theorem levQ_top_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  intro B X I a
  choose N hN using fun P : I.Q a => exists_dep_eq_exp P.1 (topDep B.R (I.cst a).M + 1)
  refine ⟨N, fun P => (hN P).le, fun P g hg => ?_⟩
  have hk : g ∈ GlobalTheory.TopStep.prinCong (B.R.N B.R.m) P.1 (topDep B.R (I.cst a).M + 1) := mem_prinCong_of_sm g (sm_of_lqPrinc (hN P) hg)
  have e : (I.Tp a).levQ B.R.m = levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) := topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  rw [e]
  exact ⟨prinCong_le_levCong _ _ _ hk, levCong_lam_prinCong _ _ _ hk⟩

end GlobalTheory.Mem.Col2.TC

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwAtStd

theorem ptY_mv_deco {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}
    (p : PtY ST SG Q y) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    (h1 : ∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) (h2 : p.1.2 ∈ y.ys d.1.N) :
    (p.mv d).1.1.deco = d := by
  have e : p.mv d = (⟨(⟨(d, p.1.1.1.2), h1⟩, p.1.2), h2⟩ : PtY ST SG Q y) := dif_pos ⟨h1, h2⟩
  rw [e]
  rfl

theorem diaPt_deco (B : Base) (X : PreX B.toPre) (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u a i).Cl) :
    (((I.atIn u a).A i).diaPt P x c).1.1.deco = DecoSet.dia1 P x ((I.stp u a i).rep c).1.1.deco :=
  ptY_mv_deco ((I.stp u a i).rep c) _ (fun Q y => ((I.stp u a i).rep c).1.1.2 Q y) ((I.stp u a i).rep c).2

theorem dil_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dil 0 P x (I.eCls0 l u a c) = I.eCls0 l u a ((I.atIn u I.mu0).dil 0 P x c) := by
  show (I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) =
    I.cl0 u a (l.idx0 a).some ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  refine (ClsZero.cl_eq_iff hI u a _ _ _ _).2 ?_
  rw [diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have e := (ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1
    (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c)))
  show _ = ClsZero.canon _ ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco
  rw [e, diaPt_deco]

theorem deco_stab_trivial (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b) (γ : UF B.fields.E (B.R.N 0)) (k : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))
    (hk : k ∈ (colLev I.Ch 0).grp) (h : ((γ, k) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco) :
    γ = 1 ∧ k = 1 := by
  have hfree : (I.stp u a 0).Free := (l.lev u a).free0
  let q : DecoF B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a)) :=
    ((γ, k, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) • p.1.1
  have hq : q.deco = p.1.1.deco := h
  have hc : ∀ P : QE I.sel (I.tup a), (p.1.1.fr P)⁻¹ * q.fr P ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    have h1 := q.2 P x
    have h2 := p.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x))
    have h3 : p.1.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
    rw [h3] at h2
    have h4 : q.1.1 = p.1.1.1.1 := hq
    rw [h4] at h1
    exact h2.symm.trans h1
  have hkG : k ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b).grp := by rw [ClsZero.levelTypePrimes_stepZero_eq_colLev hI]; exact hk
  let qq : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a)) := fun P => ⟨(p.1.1.fr P)⁻¹ * q.fr P, hc P⟩
  have htop : ∀ Θ : LevQFam B.fields.E B.fields.K (B.R.N 0) (QE I.sel (I.tup a)), Θ = LevQFam.top _ _ _ _ → qq ∈ Θ.grp := by
    rintro _ rfl
    intro P _
    trivial
  have hqQ := htop _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a b)
  have key : ∀ (y : Ys B.fields (B.R.N 0)), y = Ys.triv _ _ → ∀ (S : Set (Sp B.fields.E (B.R.N 0))) N, S ∈ y.ys N → S = ∅ := by
    rintro _ rfl S N hS
    exact hS
  have hp0 : p.1.2 = ∅ := key _ (ClsZero.ys0 a) _ _ p.2
  let g : (I.stp u a 0).G b := (γ, ⟨k, hkG⟩, ⟨qq, hqQ⟩)
  have hg : (I.stp u a 0).act b g p = p := by
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) P)⁻¹.1))⁻¹ = p.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · show (fun v => γ.1 v) '' p.1.2 = p.1.2
      rw [hp0, Set.image_empty]
  have e := hfree b g p hg
  exact ⟨congrArg Prod.fst e, congrArg (fun g : (I.stp u a 0).G b => (g.2.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) e⟩

theorem chrG_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (L Λ Λ' : LevFam E K n SG) (h : Λ = L) (h' : Λ' = L) (k : Λ.grp) (k' : Λ'.grp) (e : k.1 = k'.1) :
    Λ.chr k = Λ'.chr k' := by
  subst h h'
  rw [Subtype.ext e]

theorem chrQ_top {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (Θ : LevQFam E K n Q) (h : Θ = LevQFam.top E K n Q) (q : Θ.grp) : Θ.chr q = 1 := by
  subst h
  unfold LevQFam.chr piChar
  erw [Finset.prod_eq_one (fun i _ => MonoidHom.one_comp _)]
  rfl

theorem dilT_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dilT B.fields.emb B.embLL 0 P x (I.eCls0 l u a c) = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 P x c := by
  show (I.stp u a 0).tr B.fields.emb B.embLL (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c))) = (I.stp u I.mu0 0).tr B.fields.emb B.embLL c.1 ((I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  set ga := (I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) with hga
  set gm := (I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c) with hgm
  have hA : ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    congrArg (fun p : (I.stp u a 0).D (I.cl0 u a (l.idx0 a).some c).1 => p.1.1.deco) ((I.stp u a 0).mv_smul (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))
  have hM : ((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    congrArg (fun p : (I.stp u I.mu0 0).D c.1 => p.1.1.deco) ((I.stp u I.mu0 0).mv_smul c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  have hRA : ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u a _).trans ((ClsZero.cl_eq_iff hI u a _ _ _ _).1 (ClsZero.cl_rep (I.stp u a 0) ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))))
  have hRM : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u I.mu0 _).trans ((ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))))
  have hT : (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco := by
    rw [diaPt_deco, diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have hR : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by rw [hRA, hRM, hT]
  rw [hR, ← hT] at hM
  have hfix : (((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))⁻¹ *
      ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by
    rw [mul_smul, hA, inv_smul_eq_iff, hM]
  have memG : ∀ Λ : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs, Λ = colLev I.Ch 0 → ∀ k : Λ.grp, k.1 ∈ (colLev I.Ch 0).grp := by
    rintro _ rfl k
    exact k.2
  have hkA := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) ga.2.1
  have hkM := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) gm.2.1
  obtain ⟨e1, e2⟩ := deco_stab_trivial B X I hI l u a (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))) (gm.1⁻¹ * ga.1) (gm.2.1.1⁻¹ * ga.2.1.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hkA) hfix
  have eγ : ga.1 = gm.1 := (inv_mul_eq_one.1 e1).symm
  have ek : ga.2.1.1 = gm.2.1.1 := (inv_mul_eq_one.1 e2).symm
  show trFr B.fields.emb B.embLL ((I.stp u a 0).gam (I.cl0 u a (l.idx0 a).some c).1 ga) ((I.stp u a 0).chr (I.cl0 u a (l.idx0 a).some c).1 ga) = trFr B.fields.emb B.embLL ((I.stp u I.mu0 0).gam c.1 gm) ((I.stp u I.mu0 0).chr c.1 gm)
  congr 1
  · show ufGL _ _ ga.1 = ufGL _ _ gm.1
    rw [eγ]
  · show (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.2 =
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.1 * (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.2
    rw [chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a _), chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 _),
      chrG_eq (colLev I.Ch 0) _ _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) ga.2.1 gm.2.1 ek]

theorem mem_Fi_of_free {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (hS : S.Free)
    (φ : S.Cl → Col2.Fr emb σ n → ℂ) : φ ∈ S.Fi emb σ lam ↔ ∀ c, φ c ∈ ValC (Gr emb σ n) lam := by
  constructor
  · intro h c
    exact (h c).1
  · intro h c
    refine ⟨h c, fun g => ?_⟩
    have hg : g.1 = 1 := hS c.1 g.1 _ g.2
    funext y
    show S.tr emb σ c.1 g.1 (φ c) y = φ c y
    rw [hg]
    simp [GStep.tr, trFr_apply, frMul_one]



theorem twAtT_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ t : TwAtT (I.tw l l0 Z) u a, t.eVT = Equiv.refl _ ∧ ∀ v (r : 𝓞 B.host.E), t.eFv v (I.resT l u a v r) = I.resT l u I.mu0 (t.eVT v) r := by
  intro B X I hI hP l Z l0 u a
  refine ⟨
    { eVT := Equiv.refl _
      eFv := fun v => RingEquiv.refl _
      psiT := fun v x => rfl
      rhoT := by
        intro v x φ
        have e1 := dil_eCls0 B X I hI l u a v x
        have e2 := dilT_eCls0 B X I hI l u a v x
        funext c y
        obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
        show (I.atIn u a).dilT B.fields.emb B.embLL 0 v x (I.eCls0 l u a c') (φ ((I.eCls0 l u a).symm ((I.atIn u a).dil 0 v x (I.eCls0 l u a c')))) y = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')) (φ ((I.atIn u I.mu0).dil 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')))) y
        simp only [e1, e2, Equiv.symm_apply_apply]
      Mu0 := by
        show (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) = Submodule.map (LinearEquiv.funCongrLeft ℂ (Col2.Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) (I.eCls0 l u a).symm).toLinearMap ((I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0))
        rw [Submodule.map_equiv_eq_comap_symm]
        ext ψ
        rw [Submodule.mem_comap, mem_Fi_of_free _ _ _ _ (l.lev u a).free0, mem_Fi_of_free _ _ _ _ (l.lev u I.mu0).free0]
        constructor
        · intro h c
          exact h _
        · intro h c
          obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
          have := h c'
          simpa using this
      duStar := rfl
      Dstar := rfl
      GamP := rfl
      tauOf := fun w hw v => rfl
      seenP := fun w hw => rfl }, rfl, fun v r => rfl⟩

end GlobalTheory.Mem.Col2.TwAtStd

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_psi0_eq_embLL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  first | exact @GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | exact GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | (intros; apply GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.move_down_level_prime_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  exact GlobalTheory.Mem.Col2.TC.dn_keeps_chart I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonempty_classMap_above_lastStep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i → Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) := by
  first | exact @GlobalTheory.Mem.Col2.TC.nonempty_clDown | exact GlobalTheory.Mem.Col2.TC.nonempty_clDown | (intros; apply GlobalTheory.Mem.Col2.TC.nonempty_clDown <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  first | exact @GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | exact GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | (intros; apply GlobalTheory.Mem.Col2.TC.spaces_in_coordinates <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (σ : E →+* E)
    (hσ : ∀ x, σ x = star x) (L : Submodule (𝓞 E) (Fin n → E)) :
    dualL σ (1 : Matrix (Fin n) (Fin n) E) L = Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  have hmem : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    rfl
  have hset : dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (Formalism.HermitianLatticesTheory.dual (hStd E n) L : Set _) := by
    ext y
    rw [SetLike.mem_coe, hmem]
    simp only [dualSet, Set.mem_setOf_eq]
    refine forall₂_congr fun x _ => ?_
    have : hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ k, star (x k) * y k := by
      simp [hform, Matrix.one_apply, hσ]
    rw [this]
  unfold dualL
  rw [hset, Submodule.span_eq]

theorem GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (L : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), LdG (I.rec7 l Z) i hi L = Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) L := by
  intro B X I hI hP l Z u a i hi L
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  unfold LdG
  rw [hG]
  exact GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual _ (fun x => rfl) L

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a := by
  first | exact @GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | exact GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | (intros; apply GlobalTheory.Mem.Col2.ResF.fv_equiv_quot <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_chains_satisfy_conditions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L := by
  first | exact @GlobalTheory.Mem.Col2.TC.ok_chains | exact GlobalTheory.Mem.Col2.TC.ok_chains | (intros; apply GlobalTheory.Mem.Col2.TC.ok_chains <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.step_gam_mem_UJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b), (I.stp u a i).gam b g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := by
  intro B X I hI hP l Z u a i hi b g
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hU := (hI.stp_ok u a i).unit b g
  show cT _ _ * _ * _ = _
  rw [hG, Matrix.mul_one]
  exact hU
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  first | exact @GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | exact GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | (intros; apply GlobalTheory.Mem.Col2.LevelLaw.atIn_ok <;> assumption)
end
