module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle424
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle335
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

theorem _root_.GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → MeasurePreserving (glue e) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_glue | exact GlobalTheory.FlagFibre.measurePreserving_glue | (intros; apply GlobalTheory.FlagFibre.measurePreserving_glue <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.LevSplitAt



theorem lev_split_at : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  classical
  set L' := L.datVt i t with hL'
  set P : Formalism.L2.DIV.Pl X.toD7.host.E := (x.1.1.1 : Formalism.L2.DIV.Pl X.toD7.host.E) with hPdef
  have hoffP : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hPc, hPn, hPq⟩ := hoffP

  obtain ⟨c, hβ⟩ := hL.is.βV i
  rw [one_pow] at hβ

  have hPg : ∀ PP ∈ (flag1L L').Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Pg = L.Pg from rfl, hL.Pg] at hPP
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L L').Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    exact Finset.mem_union.2 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hm : PP ∈ sgL X I U t := hPP.elim (hPg PP) (hQ PP)
    refine ⟨fun e => hPn ?_, fun hc => hPq PP ?_ ?_⟩
    · subst e; simp [hm]
    · simp [hm]
    · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hPc
  have hpi : IsPrimeIdem P e (e + cA X.toD7 e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Vc X.toD7 i)).2.2.1 P e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 X.toD7.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split (Vc X.toD7 i) (L.βV i) (L.ΛV i) 1 (flag1L L') hβ).2 P e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift (Vc X.toD7 i) j
  have hj' : GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) g ∈ (levEnv (Vc X.toD7 i) (L.βV i) L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₁, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₂, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp (Vc X.toD7 i) hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl (Vc X.toD7 i) _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i))

end GlobalTheory.Mem.R3.LiftBrg.LevSplitAt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section



namespace GlobalTheory.Mem.R3.LiftBrg.FrameEquiv

theorem castGL_castGL_symm {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin n) R) :
    castGL h (castGL h.symm x) = x := by
  subst h
  ext i j
  simp [castGL]

theorem bc_swapAE_injective (D : D7) (m : ℕ) :
    Function.Injective (Formalism.UG.bc (n := Fin m) (swapAE D)) := by
  intro a b h
  have hs : Function.Injective (swapAE D) := fun x y hxy =>
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective hxy
  ext i j
  have := congrArg (fun g : GL (Fin m) (Formalism.IndefR.Lev.EAf D) => g.val i j) h
  exact hs this

theorem frame_equiv : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  intro X px I hX U Xg tr L i t A k hF
  obtain ⟨-, -, h3, hk, -, -⟩ := hF
  set V := Vc X.toD7 i
  set h := rkEq X i
  set G := Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV
  let c : Bridge.Gf V →* GL (Fin X.B.R.nV) (EA X) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE X.toD7)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, (A * k)⁻¹ * c g * (A * k) ∈ G := by
    intro g
    have hUA : Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _) ∈ UA X.toD7.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    have hx : A⁻¹ * c g * A ∈ G := by
      rw [h3]
      have e : A * (A⁻¹ * c g * A) * A⁻¹ = c g := by group
      rw [e, hc, castGL_castGL_symm]
      exact hUA
    have e2 : (A * k)⁻¹ * c g * (A * k) = k⁻¹ * (A⁻¹ * c g * A) * k := by group
    rw [e2]
    exact G.mul_mem (G.mul_mem (G.inv_mem hk) hx) hk
  let ψ : Bridge.Gf V →* G :=
    { toFun := fun g => ⟨(A * k)⁻¹ * c g * (A * k), hmem g⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp only [map_mul, Subgroup.coe_mul]; group }
  have hψ : ∀ g, ((ψ g : G) : GL (Fin X.B.R.nV) (EA X)) = (A * k)⁻¹ * c g * (A * k) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) hab
    simp only [hψ, mul_left_inj, mul_right_inj] at e
    rw [hc, hc] at e
    have e' := (castGL h.symm).injective e
    exact Subtype.ext (bc_swapAE_injective X.toD7 V.rank e')
  have hsurj : Function.Surjective ψ := by
    intro u
    have hku : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hk u.2) (G.inv_mem hk)
    have hw := (h3 _).1 hku
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, ?_⟩
    ext1
    rw [hψ, hc]
    change (A * k)⁻¹ * castGL h.symm (finE V κ) * (A * k) = _
    rw [hκ, castGL_castGL_symm h.symm]
    group
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let Ψ := MulEquiv.ofBijective ψ hbij
  refine ⟨Ψ.symm, fun u => ?_⟩
  have e0 : ψ (Ψ.symm u) = u := Ψ.apply_symm_apply u
  have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) e0
  simp only [hψ] at e
  rw [← hc, ← e]
  group

end GlobalTheory.Mem.R3.LiftBrg.FrameEquiv
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet


open _root_.Formalism.L2.Col in
theorem prod_diag_inv {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) (π : 𝓞 E) (d : ℕ) (hd : d ≤ n) :
    ∏ i : Fin n, (mhlDiag n π d i)⁻¹ = (mhlA π)⁻¹ ^ d := by
  have h1 : ∀ i : Fin n, (mhlDiag n π d i)⁻¹ = (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) i.1 := by
    intro i
    unfold mhlDiag
    by_cases h : i.1 < d <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) n,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.range n).filter (fun j => j < d) = Finset.range d := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem idem_mul_pow {R : Type} [CommRing R] {e : R} (hee : e * e = e) (x : R) (d : ℕ) : e * (e * x) ^ d = e * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    rw [show e * x ^ d * (e * x) = (e * e) * (x ^ d * x) by ring, hee]

theorem pow_mem_int {D : D7} {x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (d : ℕ) :
    x ^ d ∈ intAE D := by
  induction d with
  | zero => rw [pow_zero]; exact GlobalTheory.HeckeConj.one_mem_intAE D
  | succ d ih => rw [pow_succ]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ih hx

theorem unit_mem {D : D7} {e a : Formalism.L2.Theta.AE D} (hee : e * e = e) (ha : finPart D (e * a) ∈ intAE D) (d : ℕ) :
    finPart D (e * a ^ d + (1 - e)) ∈ intAE D := by
  have he : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  rw [← idem_mul_pow hee a d, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, RingHom.map_pow]
  exact add_mem (GlobalTheory.HeckeConj.mul_mem_intAE D he (pow_mem_int ha d)) (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) he)

theorem det_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.det (castGL h g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, castGL, Matrix.det_reindex_self]

theorem det_fin {D : D7} (V : HSp D) (α : GA D V) : finPart D (Formalism.L2.Theta.mt V α).det = (finHom V α).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_swap {D : D7} {m : ℕ} (g : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    swapAE D g.val.det = (Formalism.UG.bc (swapAE D) g).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_cast {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) : (castGL h g).val.det = g.val.det := by
  have := congrArg Units.val (det_castGL h g)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem det_conj_inv {R : Type} [CommRing R] {n : ℕ} (C η : GL (Fin n) R) : ((C * η * C⁻¹)⁻¹).val.det = (η⁻¹).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  rw [map_inv, map_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem cast_inv {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) :
    castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)))⁻¹ := by
  rw [map_inv (finHom V) α, map_inv (Formalism.UG.bc (swapAE D)), map_inv (castGL h.symm)]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_transport {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) (C η : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (hC : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * η * C⁻¹) :
    swapAE D (finPart D (Formalism.L2.Theta.mt V α⁻¹).det) = (η⁻¹).val.det := by
  have hg : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (C * η * C⁻¹)⁻¹ := by
    rw [cast_inv V h α, hC]
  rw [det_fin V α⁻¹, det_swap (finHom V α⁻¹), ← det_cast h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)), hg,
    det_conj_inv C η]

theorem prV_det_eta {D : D7} (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 D.host.F)) {π : 𝓞 D.host.E} (hπ0 : π ≠ 0)
    (d : ℕ) :
    Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val.det -
        Formalism.L2.Col.iA D.host.F D.host.E (∏ k : Fin n, (Formalism.L2.Col.mhlDiag n π d k)⁻¹)) = 0 := by
  have hdiag : ∀ i j : Fin n, Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val i j) =
      Formalism.UG.prV v ((Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) i j) := by
    intro i j
    rw [Formalism.L2.Col.mhl_prV_eta_inv, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hm : (Formalism.UG.prV v).mapMatrix (((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val =
      (Formalism.UG.prV v).mapMatrix (Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) :=
    Matrix.ext hdiag
  rw [RingHom.map_sub, RingHom.map_det, hm, ← RingHom.map_det, Matrix.det_diagonal,
    map_prod (Formalism.L2.Col.iA D.host.F D.host.E), sub_self]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem hom_mul_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (d : ℕ) :
    f ((a * b) ^ d) = f a ^ d * f b ^ d := by
  rw [map_pow, map_mul, mul_pow]

theorem final_alg {R : Type} [CommRing R] {e Δ c X W : R} (hee : e * e = e) (key : e * Δ = e * c) (hc : c = X * W) :
    e * Δ = e * W * (e * X + (1 - e)) := by
  linear_combination key + e * hc + (W - W * X) * hee

theorem swap_inj {D : D7} {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (h : swapAE D x = swapAE D y) :
    x = y :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem idem_eq_of_swap {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {x c : Formalism.L2.Theta.AE D}
    (h : swapAE D (finPart D e) * swapAE D (finPart D x) = swapAE D (finPart D e) * swapAE D (finPart D c)) :
    e * x = e * c := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]
  · apply swap_inj
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
    exact h

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_clause : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  intro D V n _ h v Pb Ut d e C α hd he hε hα hC
  have hπ0 : ((Ut.π : 𝓞 D.host.E) : D.host.E) ≠ 0 := Formalism.L2.Col.mhl_alg_ne Ut.hπ0
  have hee : e * e = e := he.1.1
  have hfe : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hinv : finPart D (e * incA D ((Ut.π : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact Ut.hπP ((he.2 Ut.π Ut.hπ0).2 hc)
  have hpi : finPart D (e * incA D (Ut.π : D.host.E)) ∈ intAE D := by
    rw [RingHom.map_mul]
    exact GlobalTheory.HeckeConj.mul_mem_intAE D hfe (AddSubgroup.subset_closure ⟨1, fun v => one_mem _, Ut.π, rfl⟩)
  have hXY : incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d = 1 := by
    rw [← mul_pow, ← RingHom.map_mul, inv_mul_cancel₀ hπ0, RingHom.map_one, one_pow]
  refine ⟨e * incA D ((Ut.π : D.host.E))⁻¹ ^ d + (1 - e), e * incA D (Ut.π : D.host.E) ^ d + (1 - e),
    unit_mem hee hinv d, unit_mem hee hpi d, ?_, ?_⟩
  · linear_combination e * hXY + ((e + 1) * (incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d) -
      e * (incA D ((Ut.π : D.host.E))⁻¹ ^ d + incA D (Ut.π : D.host.E) ^ d) + (e - 1)) * hee
  ·
    have hdet := det_transport V h α C _ hC
    have hε' := hε _ (prV_det_eta (D := D) n v Ut.hπ0 d)
    rw [mul_sub, sub_eq_zero, prod_diag_inv n Ut.π d hd, Formalism.L2.Col.mhlA_inv Ut, ← hdet] at hε'
    have key : e * (Formalism.L2.Theta.mt V α⁻¹).det = e * incA D ((((Ut.π : D.host.E))⁻¹ *
        ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) :=
      idem_eq_of_swap he.1 hε'
    have hc : incA D ((((Ut.π : D.host.E))⁻¹ * ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) =
        incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d :=
      hom_mul_pow (incA D) _ _ d
    exact final_alg hee key hc

end GlobalTheory.Mem.R3.LiftBrg.EtaDet
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



namespace GlobalTheory.Mem.R3.LiftLatStd

theorem hLat_eq_decoPt_N : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  intro X i Λ hΛ SG eG hx x
  have hΛ' := hΛ
  obtain ⟨c, hfr, -⟩ := hΛ'
  rw [GlobalTheory.HLatMove.hLat_eq_span hΛ, Formalism.L2.Col.decoPt_mk]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists _ _ _ _ _ x.2)]
  set h := eG x with hh
  set g := Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E)) with hg
  have hxg : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = LiftBrg.castGL (LiftBrg.rkEq X i).symm g := (hx x).symm
  have hL : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      (h.1⁻¹).1 *ᵥ (fun j => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y j) ∈
          GlobalTheory.AdLat.hat X.toD7.host.F (Λ : Set (Fin (Vc X.toD7 i).rank → X.toD7.host.E)) ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    have e : ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) =
        fun j => Algebra.TensorProduct.comm X.toD7.host.F _ X.toD7.host.E
          (((h.1⁻¹).1 *ᵥ (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y k)) j) := by
      rw [hg, ← map_inv]
      funext j
      change _ = swapAE X.toD7 _
      rw [RingHom.map_mulVec (swapAE X.toD7)]
      rfl
    have e1 := hfr ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)))
    rw [inv_one, Units.val_one, Matrix.one_mulVec] at e1
    rw [← e1, e]
    constructor
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
      simpa only [AlgEquiv.symm_apply_apply] using this
  have hR : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      y ∈ (Formalism.UG.CS.globLat (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (Formalism.L2.Col.stdLat X.toD7.host.E X.B.R.nV)).map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Formalism.L2.Col.mem_globLat]
    unfold Formalism.L2.Col.pullV
    rw [hxg, ← map_inv]
    simp only [LiftBrg.castGL, Units.coe_mapEquiv, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
    simp only [LinearMap.funLeft_apply]
    have e2 : ∀ (M : Matrix (Fin (Vc X.toD7 i).rank) (Fin (Vc X.toD7 i).rank) (Lev.EAf X.toD7)),
        ((Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm)).toRingEquiv.toMulEquiv M) *ᵥ
          (fun a => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y (finCongr (LiftBrg.rkEq X i) a))) =
        fun a => (M *ᵥ fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)) (finCongr (LiftBrg.rkEq X i) a) := by
      intro M
      change Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm) M *ᵥ _ = _
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      funext a
      simp [Function.comp_def]
    rw [e2]
    exact ⟨fun H j => by simpa using H ((finCongr (LiftBrg.rkEq X i)).symm j), fun H a => H _⟩
  refine le_antisymm (Submodule.span_le.2 fun y hy => (hR y).2 ((hL y).1 hy)) fun y hy => Submodule.subset_span ((hL y).2 ((hR y).1 hy))

end GlobalTheory.Mem.R3.LiftLatStd
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  first | exact @GlobalTheory.HwEigen.mu_eq_of_upper_eigen | exact GlobalTheory.HwEigen.mu_eq_of_upper_eigen | (intros; apply GlobalTheory.HwEigen.mu_eq_of_upper_eigen <;> assumption)
end
