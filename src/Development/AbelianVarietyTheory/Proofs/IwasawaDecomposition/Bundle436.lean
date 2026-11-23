module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle401
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle417
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle420
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

theorem ptEmb_iff_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  intro B X I hI hP l Z u a z
  have hsg : sgTG (D := I.rec7 l Z) (I.fm l u a) = (I.perIn u a).sgT := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg
  exact rat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP (VV_shW B.wts.sgW _) hsh z

end GlobalTheory.Mem.Col2.TwP

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie




theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.rowFormMetric_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  first | exact @GlobalTheory.Mem.Df.ipMt_eq_cSum | exact GlobalTheory.Mem.Df.ipMt_eq_cSum | (intros; apply GlobalTheory.Mem.Df.ipMt_eq_cSum <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem underPl_conjP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (P : HeightOneSpectrum (𝓞 E)) : underPl F (conjPrime₂ P) = underPl F P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [underPl_asIdeal, underPl_asIdeal, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, rll_cO_algebraMap hc]

theorem conjP_notMem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ1 : ∀ P : Q, conjPrime₂ P.1 ≠ P.1)
    (hQ2 : ∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') : ∀ P ∈ Q, conjPrime₂ P ∉ Q := by
  intro P hP hP'
  have h := hQ2 ⟨P, hP⟩ ⟨conjPrime₂ P, hP'⟩ (underPl_conjP hc P).symm
  exact hQ1 ⟨P, hP⟩ (congrArg Subtype.val h).symm

theorem red_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] (a : 𝓞 E) (ha : a ≠ 0) {u : GL (Fin n) (AfE F E)} (hu : u ∈ UAd hc n)
    (h : GlobalTheory.Mem.ColAd.CongOne a u) :
    ∃ hS : u ∈ St (1 : GL (Fin n) (AfE F E)), ∀ w : HeightOneSpectrum (𝓞 E), a ∈ w.asIdeal →
      redAt (1 : GL (Fin n) (AfE F E)) w ⟨u, hS⟩ = 1 := by
  classical
  have hca : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) *
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by simpa using ha), map_one]
  have hs : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j = (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j +
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * (⟨_, h i j⟩ : Formalism.L2.Herm.intAf F E) := by
    intro i j
    show _ = _ + _ * (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ * _)
    rw [← mul_assoc, hca, one_mul]
    ring
  obtain ⟨s, hs⟩ : ∃ s : Fin n → Fin n → Formalism.L2.Herm.intAf F E, ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j + Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * s i j :=
    ⟨fun i j => ⟨_, h i j⟩, hs⟩
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hi : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [hs]
    exact add_mem (hone i j) (mul_mem (iA_mem a) (s i j).2)
  have hSt := rlt_mem_St hc n hu hi
  obtain ⟨y, hy, hred⟩ := St_one_int hSt
  refine ⟨hSt, fun P hP => ?_⟩
  apply Units.ext
  ext i j
  rw [hred P i j]
  have e : y i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j + oToS F E a * s i j := by
    apply Subtype.ext
    rw [← hy, hs]
    simp only [Subring.coe_add, Subring.coe_mul]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  rw [e, map_add (f := _), map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul, add_zero]
  show _ = (1 : Matrix (Fin n) (Fin n) (kP P)) i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.SeeSaw.TwLev.Approx

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem rd_all : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  intro F E K _ _ _ _ _ _ _ hc n _ SG Q J hJ T f bad S Λ emb HQ lamQ hQ1 hQ2 hO hR
  subst hJ
  classical
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hQc := conjP_notMem hc hQ1 hQ2
  have h1U : (1 : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) ∈
      {x : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} := S.U.one_mem
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ _ _).1 (S.U_open.mem_nhds h1U)
  obtain ⟨m₀, hm₀, hm₀N⟩ := GlobalTheory.T.congruenceOne_matrices_mem_nhds_one (F := F) (E := E) n (V ∩ {u | ∀ κ : S.U, κ.1 = u → S.chi κ = 1})
    (Filter.inter_mem hV hO)
  set m : ℕ := m₀ * ∏ w ∈ SG ∪ Q, Ideal.absNorm w.asIdeal with hm
  have hmpos : 0 < m := Nat.mul_pos hm₀ (Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot))
  have hmw : ∀ w ∈ SG ∪ Q, ((m : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    intro w hw
    obtain ⟨k, hk⟩ : Ideal.absNorm w.asIdeal ∣ m := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hw) _
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  intro z _ hz hzU
  obtain ⟨g, hgU, hgR, hc1, hc2⟩ := GlobalTheory.T.exists_rationalAtPrimes_unitary_congruentOne hc hQc m hmpos (fun P hP => hmw P (Finset.mem_union_right _ hP)) z hzU hz
  set u := z⁻¹ * g with hu
  have huU : u ∈ UAd hc n := mul_mem (inv_mem hzU) hgU
  have huN := hm₀N m (Dvd.intro _ rfl) hmpos u hc1 hc2
  have huS : u ∈ S.U := hVsub (a := ⟨u, huU⟩) huN.1
  have hchiu : S.chi ⟨u, huS⟩ = 1 := huN.2 ⟨u, huS⟩ rfl
  obtain ⟨huSt, hred⟩ := red_eq_one hc (m : 𝓞 E) (by exact_mod_cast hmpos.ne') huU hc1
  have hzg : g = z * u := by rw [hu, mul_inv_cancel_left]
  have hgSt : g ∈ St (1 : GL (Fin n) (AfE F E)) := hzg ▸ mul_mem hz huSt
  have hredg : ∀ w ∈ SG ∪ Q, redAt (1 : GL (Fin n) (AfE F E)) w ⟨g, hgSt⟩ = redAt 1 w ⟨z, hz⟩ := by
    intro w hw
    have e : (⟨g, hgSt⟩ : St (1 : GL (Fin n) (AfE F E))) = ⟨z, hz⟩ * ⟨u, huSt⟩ := Subtype.ext hzg
    rw [e, map_mul, hred w (hmw w hw), mul_one]
  obtain ⟨hiff, hchi⟩ := hR g hgR hgSt hgU
  have hgz : g ∈ S.U ↔ z ∈ S.U := by
    rw [hzg]
    exact ⟨fun h => by simpa using mul_mem h (inv_mem huS), fun h => mul_mem h huS⟩
  have hSGr : ∀ w : SG, redAt (1 : GL (Fin n) (AfE F E)) w.1 ⟨g, hgSt⟩ = redAt 1 w.1 ⟨z, hz⟩ :=
    fun w => hredg w.1 (Finset.mem_union_left _ w.2)
  have hQr : ∀ P : Q, redAt (1 : GL (Fin n) (AfE F E)) P.1 ⟨g, hgSt⟩ = redAt 1 P.1 ⟨z, hz⟩ :=
    fun P => hredg P.1 (Finset.mem_union_right _ P.2)
  refine ⟨?_, ?_⟩
  · rw [← hgz, hiff]
    simp only [hSGr, hQr]
  · intro hU h h'
    have hgU' : g ∈ S.U := hgz.2 hU
    have e1 := hchi hgU' (fun w => (hSGr w).symm ▸ h w) (fun P => (hQr P).symm ▸ h' P)
    have e2 : S.chi ⟨g, hgU'⟩ = S.chi ⟨z, hU⟩ := by
      have : (⟨g, hgU'⟩ : S.U) = ⟨z, hU⟩ * ⟨u, huS⟩ := Subtype.ext hzg
      rw [this, map_mul, hchiu, mul_one]
    rw [← e2, e1]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [show (⟨_, (hSGr w).symm ▸ h w⟩ : (Λ w).H) = ⟨_, h w⟩ from Subtype.ext (hSGr w)]
    · refine Finset.prod_congr rfl fun P _ => ?_
      rw [show (⟨_, (hQr P).symm ▸ h' P⟩ : HQ P) = ⟨_, h' P⟩ from Subtype.ext (hQr P)]

end GlobalTheory.SeeSaw.TwLev.Approx
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  exact @GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

theorem conjLoc_exists_split (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    ∃ s' : SplitPlace D.host.E, s'.w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  refine ⟨⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩, ?_⟩
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem conjLoc (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (h : IsConjPl D.host w s.w) : ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  obtain ⟨s', rfl⟩ := conjLoc_exists_split D s w h
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π s'
  exact ⟨_, s', σ, rfl, hσ, HEq.rfl⟩

end GlobalTheory.AutQuot
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_coordinate_model_of_algWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  first | exact @GlobalTheory.AutQuot.Model.exists_model | exact GlobalTheory.AutQuot.Model.exists_model | (intros; apply GlobalTheory.AutQuot.Model.exists_model <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.automorphic_rep_cm_quotient_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n),
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  first | exact @GlobalTheory.AutModel.exists_autRepM | exact GlobalTheory.AutModel.exists_autRepM | (intros; apply GlobalTheory.AutModel.exists_autRepM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowWeight

lemma isWtOfPar_eq {N n : ℕ} (h : N = n) {lam : DomWeight N} {S : SPar} (hS : Bridge.IsWtOfPar lam S)
    (hs : ∀ x ∈ S, x.2 = true) (c' : Fin n → ℚ) (hc' : StrictAnti c') (hm' : ∀ i, (c' i, true) ∈ S) (i : Fin N) :
    (lam.w i : ℚ) = c' (Fin.cast h i) - rhoVec n (Fin.cast h i) := by
  subst h
  obtain ⟨hcard, c, hc, hm, hw⟩ := hS
  have key : ∀ d : Fin N → ℚ, StrictAnti d → (∀ i, (d i, true) ∈ S) → Set.range d = {x | (x, true) ∈ S} := by
    intro d hd hdm
    have h1 : Finset.univ.image (fun i => (d i, true)) = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hdm i
      · rw [Finset.card_image_of_injective _ (fun x y h => hd.injective (Prod.ext_iff.mp h).1), hcard]
        simp
    ext x
    rw [← h1]
    simp
  have hm2 : ∀ i, (c i, true) ∈ S := fun i => by
    obtain ⟨s, hs'⟩ := hm i
    have : s = true := hs _ hs'
    rwa [this] at hs'
  have e : c = c' := (hc.range_inj hc').1 ((key c hc hm2).trans (key c' hc' hm').symm)
  rw [hw, e]
  rfl

lemma sgHC_mem {R : Ranks} (P : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    ∃ x, GlobalTheory.ForcedWeights.entry P x = (Formalism.L2.Col.RowPar.of P).sgHC n - Formalism.L2.Col.RowPar.sh R := by
  have hk := R.m_add_three_le_k
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · refine ⟨.inl ⟨n, h1⟩, ?_⟩
    rw [Formalism.L2.Col.RowPar.sgHC_lo _ h1, Formalism.L2.Col.RowPar.vb_lo _ h1]
    simp [GlobalTheory.ForcedWeights.entry]
  · obtain ⟨B, ρ, hρ, rfl⟩ : ∃ B ρ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ := by
      refine ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (by omega), ?_⟩
      have := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
      rw [Nat.mul_comm] at this
      omega
    have hBm : B < R.m := by
      apply Nat.lt_of_mul_lt_mul_right (a := R.t + 1)
      omega
    rcases ρ with _ | ρ
    · refine ⟨.inr (.inl ⟨B, hBm⟩), ?_⟩
      rw [Nat.add_zero, Formalism.L2.Col.RowPar.sgHC_b, Formalism.L2.Col.RowPar.bAt_of _ hBm]
      simp [GlobalTheory.ForcedWeights.entry]
    · refine ⟨.inr (.inr (⟨B, hBm⟩, ⟨ρ, by omega⟩)), ?_⟩
      rw [Formalism.L2.Col.RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega), Formalism.L2.Col.RowPar.eAt_of _ hBm]
      simp only [GlobalTheory.ForcedWeights.entry]
      push_cast
      ring

lemma sgHC_strictAnti {R : Ranks} (P : HCParam R) :
    StrictAnti fun i : Fin (R.N R.m - 1) => (Formalism.L2.Col.RowPar.of P).sgHC i.1 - Formalism.L2.Col.RowPar.sh R := by
  intro i j hij
  have h := Formalism.L2.Col.anti_sub_rho (N := R.N R.m - 1) (Formalism.L2.Col.RowPar.of P).sgHC
    (fun _ hn => Formalism.L2.Col.RowPar.sgHC_step P hn) hij.le
  have h2 : (i.1 : ℚ) < (j.1 : ℚ) := by exact_mod_cast (show i.1 < j.1 from hij)
  simp only [rhoVec] at h ⊢
  linarith

theorem lamRdef_eq (D : D7) (h : D.sp.X'.rank = D.R.N D.R.m - 1) (τ : D.what₂.Tau) (i : Fin D.sp.X'.rank) :
    (Bridge.lamRdef (Ptw D) τ).w i = (Formalism.L2.Col.RowPar.of (D.hc τ)).sgTrue.w (Fin.cast h i) := by
  have hF := GlobalTheory.ForcedWeights.lamRForced D τ
  rw [GlobalTheory.ForcedWeights.dpar_eq] at hF
  have h1 := isWtOfPar_eq h hF (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      rfl) _ (sgHC_strictAnti (D.hc τ)) (fun a => by
      obtain ⟨x, hx⟩ := sgHC_mem (D.hc τ) a.1 a.2
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [hx]⟩) i
  rw [← Formalism.L2.Col.RowPar.sgTrue_eq] at h1
  exact_mod_cast h1

theorem lamRdef_eq_sgTrue : ∀ (X : Stages) (τ : X.B.fields.Tau) (i : Fin X.toD7.sp.X'.rank), (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w (Fin.cast (RowAd.rank_X' X) i) :=
  fun X τ i => lamRdef_eq X.toD7 (RowAd.rank_X' X) τ i

end GlobalTheory.Mem.R3.RowWeight
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide | exact GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide | (intros; apply GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide <;> assumption)
end
