module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Formalism.LocalToGlobal.UnitaryNorms.CharExHost
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle730
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle727
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle728
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle650
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.PeriodQuot

theorem iter_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) (a b : A) : f^[j] (a * b) = f^[j] a * f^[j] b := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iter_one {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) : f^[j] (1 : A) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_one]

theorem iter_natCast_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j m q : ℕ) (a : A) : f^[j] ((m : A) ^ q * a) = (m : A) ^ q * f^[j] a := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem galois_periodRatio_mem_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  intro l _ P AI hT K x hx hn h1 h2 hj g
  obtain ⟨u, rfl⟩ := hx
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  have npos : 0 < n := by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos
  set y : P.R.B := ((u⁻¹ : (P.R.B)ˣ) : P.R.B) with hy
  have huy : (u : P.R.B) * y = 1 := u.mul_inv
  set c : P.R.B := P.actQ (g : GQ l) u * y with hc
  have hcx : P.actQ (g : GQ l) u = c * u := by rw [hc, mul_assoc, u.inv_mul, mul_one]
  have hcomm : ∀ b, P.φB (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) (P.φB b) := by
    intro b
    have := (P.PD K).φ_comm g b
    rwa [P.PD_φ, P.PD_actB, P.PD_actB, P.PD_φ] at this
  have hcommj : ∀ j b, (⇑P.φB)^[j] (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) ((⇑P.φB)^[j] b) :=
    fun j b => (Function.Commute.iterate_left (f := ⇑P.φB) (g := ⇑(P.actQ (g : GQ l)))
      (fun b => hcomm b) j) b

  have hlB : IsUnit ((l : ℕ) : P.R.B) := by
    have h0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (isUnit_iff_ne_zero.mpr h0).map (algebraMap ℚ_[l] P.R.B)
    simpa using this

  have hφc : (⇑P.φB)^[n] c = c := by
    have hu : IsUnit ((l : P.R.B) * u) := hlB.mul u.isUnit
    apply hu.mul_left_injective
    show (⇑P.φB)^[n] c * ((l : P.R.B) * u) = c * ((l : P.R.B) * u)
    rw [← hn, ← iter_mul, ← hcx, hcommj, hn, map_mul, map_natCast, hcx]
    ring

  have hpow : ∀ q : ℕ, (⇑P.φB)^[n * q] (u : P.R.B) = (l : P.R.B) ^ q * u := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hn,
        show (l : P.R.B) * (u : P.R.B) = (l : P.R.B) ^ 1 * u by rw [pow_one],
        iter_natCast_mul, ih, ← mul_assoc, ← pow_add, add_comm 1 q]
  have hsmul : ∀ (q : ℕ) (z : P.R.B), P.ιB ((l : P.R.B) ^ q * z) =
      (((l : ↥K.1) ^ q : ↥K.1)) • P.ιB z := by
    intro q z
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  have hne : ∀ q : ℕ, ((l : ↥K.1) ^ q : ↥K.1) ≠ 0 := fun q =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hdeg : ∀ j : ℕ, ∃ d : ℤ, P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∈ (P.PD K).Fil d ∧
      P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∉ (P.PD K).Fil (d + 1) := by
    intro j
    have hj_eq : j = j % n + n * (j / n) := (Nat.mod_add_div j n).symm
    have hw : (⇑P.φB)^[j] (u : P.R.B) = (l : P.R.B) ^ (j / n) * (⇑P.φB)^[j % n] u := by
      conv_lhs => rw [hj_eq]
      rw [Function.iterate_add_apply, hpow, iter_natCast_mul]
    rw [hw, hsmul]
    rcases Nat.eq_zero_or_pos (j % n) with h0 | hr
    · refine ⟨1, ?_, ?_⟩
      · rw [h0, Function.iterate_zero_apply]
        exact Submodule.smul_mem _ _ h1
      · rw [h0, Function.iterate_zero_apply, Submodule.smul_mem_iff _ (hne _)]
        simpa using h2
    · obtain ⟨ha, hb⟩ := hj (j % n) hr (Nat.mod_lt _ npos)
      refine ⟨0, Submodule.smul_mem _ _ ha, ?_⟩
      rw [Submodule.smul_mem_iff _ (hne _)]
      simpa using hb
  have hF : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0 := by
    intro j
    obtain ⟨d, hd1, hd2⟩ := hdeg j
    have hinv : P.ιB ((⇑P.φB)^[j] (u : P.R.B)) * P.ιB ((⇑P.φB)^[j] y) = 1 := by
      rw [← map_mul, ← iter_mul, huy, iter_one, map_one]
    have hyF := GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree l P AI hT K d _ _ hinv hd1 hd2
    have hgF : P.ιB (P.actQ (g : GQ l) ((⇑P.φB)^[j] (u : P.R.B))) ∈ (P.PD K).Fil d := by
      have := (P.PD K).ι_comm g ((⇑P.φB)^[j] (u : P.R.B))
      rw [P.PD_ι, P.PD_actB, P.PD_ι] at this
      rw [this]
      exact (P.PD K).Fil_G g d _ hd1
    have := (P.PD K).Fil_mul d (-d) _ _ hgF hyF
    rw [add_neg_cancel] at this
    rw [hc, iter_mul, hcommj, map_mul]
    exact this
  obtain ⟨a, ha⟩ := GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil l P AI hT K c hφc hF
  exact ⟨a, by rw [hcx, ha]⟩

end GlobalTheory.PeriodQuot
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), IsUnif L s.v ϖ → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f := by
  first | exact @GlobalTheory.HeckeScalarSph.tN_scalar | exact GlobalTheory.HeckeScalarSph.tN_scalar | (intros; apply GlobalTheory.HeckeScalarSph.tN_scalar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

open Formalism.L2.Host

variable {D : D7} {T N : Type}

theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) : (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

theorem trivOn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ : HChar E}
    (h : χ.TrivOn F) (a : ℕ) : (χ ^ a).TrivOn F := by
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · have h1 := h.1 v k
    simp only [HChar.resFin, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [locK_pow]
    rw [Finset.prod_pow, h1, one_pow]
  · have h1 := h.2 w k
    simp only [HChar.resInf, HChar.locInf, MonoidHom.finsetProd_apply, MonoidHom.comp_apply] at h1 ⊢
    simp only [pow_apply']
    rw [Finset.prod_pow, h1, one_pow]

theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) : (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) : ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : χ.OrderDvd n) :
    c ^ n = 1 := by
  have h1 := chrEq_pow h n
  rw [show χ ^ n = 1 from hn] at h1
  exact MonoidHom.ext fun x => GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x

theorem exists_pow_aut (τ : ℂ ≃+* ℂ) {n : ℕ} (hn : 0 < n) : ∃ a, a < n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ a := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨a, ha, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ (Complex.exp (2 * Real.pi * Complex.I / n)))
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  refine ⟨a, ha, fun z hz => ?_⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  rw [map_pow, ← h, ← pow_mul, ← pow_mul, mul_comm a b]

theorem exists_conj_pow {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) : ∃ n : ℕ, ∀ τ : ℂ ≃+* ℂ, ∃ a, a < n ∧
    (∀ x, (((L.xi t ^ a) x : Circle) : ℂ) = τ ((L.xi t x : Circle) : ℂ)) ∧ ∃ b, (L.xiH t ^ a) ^ b = L.xiH t := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : ∀ x, ((L.xi t x : Circle) : ℂ) ^ n = 1 := fun x => by
    have := DFunLike.congr_fun (pow_eq_one_of_chrEq (hL.xi t) ho) x
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    exact (map_pow Circle.coeHom _ _).symm.trans (congrArg _ this)
  have h2 : ∀ a x, (((L.xi t ^ a) x : Circle) : ℂ) = ((L.xi t x : Circle) : ℂ) ^ a := fun a x => by
    rw [MonoidHom.pow_apply]; exact map_pow Circle.coeHom _ _
  refine ⟨n, fun τ => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_pow_aut τ hn
  obtain ⟨b, -, h'⟩ := exists_pow_aut τ.symm hn
  refine ⟨a, ha, fun x => by rw [h2, h _ (h1 x)], b, ?_⟩
  have e : (L.xi t ^ a) ^ b = L.xi t := MonoidHom.ext fun x => Circle.ext (by
    rw [← pow_mul, h2, pow_mul, ← h _ (h1 x), ← h' _ (by rw [← map_pow, h1, map_one]), RingEquiv.symm_apply_apply])
  exact GlobalTheory.ChrEqUnique.hchar_unique D (L.xi t) _ _ (e ▸ chrEq_pow (chrEq_pow (hL.xi t) a) b) (hL.xi t)

end GlobalTheory.ConjExt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrivOnRead

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infIdele_snd_one {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem fst_prod_apply {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w :=
  map_prod ((Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) f s

theorem snd_prod {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem ideleMap_inf (w : InfinitePlace F) (k : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (infIdele F w (atInf w k)) = CharEx.aFi (L := E) F w k := by
  classical
  refine Units.ext (Prod.ext (funext fun w' => ?_) ?_)
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 w' = _
    rw [CharEx.aFi, Units.coe_prod, fst_prod_apply]
    change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
      ((infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 (w'.comap (algebraMap F E))) = _
    by_cases hw : w'.comap (algebraMap F E) = w
    · have hm : w' ∈ aboveInf (L := E) F w := by simp [aboveInf, hw]
      rw [Finset.prod_eq_single_of_mem w' hm (fun w'' _ h => infIdele_fst_ne E w'' w' (Ne.symm h) _),
        infIdele_fst_self]
      subst hw
      rw [infIdele_fst_self]
      change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
        (algebraMap F _ (k : F)) = algebraMap E _ (algebraMap F E (k : F))
      rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.algebraMap_apply,
        AbsoluteValue.Completion.map_coe]
      rfl
    · rw [infIdele_fst_ne F w _ hw, map_one]
      refine (Finset.prod_eq_one fun w'' hw'' => infIdele_fst_ne E w'' w' ?_ _).symm
      rintro rfl
      simp [aboveInf] at hw''
      exact hw hw''
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).2 = _
    rw [CharEx.aFi, Units.coe_prod, snd_prod]
    rw [Finset.prod_eq_one fun w'' _ => infIdele_snd_one w'' _]
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)

end General


open GlobalTheory.CharTransport in

theorem exists_hom_tmul (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ a x, Θ (a ⊗ₜ[D.host.F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hΘ, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem trivOn_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  intro D c χ hc ha
  have hχ := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D c χ hc
  obtain ⟨Θ, hΘc, hΘt, hinc, hloc⟩ := exists_hom_tmul D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΘc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have hc' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, hloc P e he]
      rw [hcoe, this]
      rfl
  have hcc : c = c' := GlobalTheory.ChrEqUnique.idc_unique D c c' χ hc hc'
  have key : ∀ a : (AF D.host.F)ˣ, χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a) = 1 := fun a => by
    have h1 : u (idF D a) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a := Units.ext (by
      change Θ ((a : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
      rw [hΘt, map_one, mul_one]
      rfl)
    have h2 := hcoe (idF D a)
    rw [← hcc, ha, h1] at h2
    exact Units.ext (by rw [← h2]; rfl)
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · rw [CharEx.resFin_eq]
    change χ.1 (GlobalTheory.Mem.Chr.locF D.host.F v k) = 1
    rw [← GlobalTheory.ToricDistribution.ideleMap_local]
    exact key _
  · rw [CharEx.resInf_eq, ← ideleMap_inf]
    exact key _

end GlobalTheory.TrivOnRead
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem _root_.GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  first | exact @GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | exact GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep | (intros; apply GlobalTheory.HyodoFin.finite_continuous_cocycles_localGaloisRep <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.blochKato_localCondition_all_localizations : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | exact GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | (intros; apply GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.BKAtQD

theorem admBK_embeddingTypeJumps : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) →
    ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := by
  intro D hBK hLit i hi w hw C
  obtain ⟨-, hTD, -⟩ := hLit i hi
  exact ⟨(hTD w hw C).1, (hTD w hw C).2,
    fun _ => TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (hBK _ _).2.2.2.1 (GlobalTheory.AdmBK.litGoodO_all _ _)⟩

end GlobalTheory.BKAtQD
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ColumnUnramified

theorem blochKatoFinite_trivialRep_unramified_columnPlaces : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  intro D i dc w hw _ C
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact GlobalTheory.T.unramified_trivial_local (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL

end GlobalTheory.ColumnUnramified
end
