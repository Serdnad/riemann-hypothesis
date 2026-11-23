module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle013
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

def bar {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (q : PtY ST SG Q y) (w : SG) :
    Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :=
  {v | ∃ z ∈ q.1.2, v = q.1.1.deco.1.be w ((qOf w.1 : X.E) • z)}

def setStab {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {h | ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  inv_mem' {a} ha v := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.MemChart
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.KerRat

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem sum_cover {K M G D G' D' : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] [MulAction G D] [Group G']
    [MulAction G' D'] [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient G' D')]
    (π : D → D') (hs : Function.Surjective π) (h1 : ∀ (g : G) d, ∃ g' : G', π (g • d) = g' • π d)
    (h2 : ∀ (g' : G') d e, g' • π d = π e → ∃ g : G, g • d = e)
    (h3 : ∀ d, Nat.card (MulAction.stabilizer G d) = Nat.card (MulAction.stabilizer G' (π d)))
    (r : MulAction.orbitRel.Quotient G D → D) (hr : ∀ q, Quotient.mk (MulAction.orbitRel G D) (r q) = q)
    (r' : MulAction.orbitRel.Quotient G' D' → D') (hr' : ∀ q, Quotient.mk (MulAction.orbitRel G' D') (r' q) = q)
    (f : D' → M) (hf : ∀ (g' : G') d, f (g' • d) = f d) :
    ∑ q, ((Nat.card (MulAction.stabilizer G (r q)) : ℕ) : K)⁻¹ • f (π (r q)) =
      ∑ q, ((Nat.card (MulAction.stabilizer G' (r' q)) : ℕ) : K)⁻¹ • f (r' q) := by
  refine Fintype.sum_bijective (fun q => Quotient.mk (MulAction.orbitRel G' D') (π (r q))) ⟨fun q q' h => ?_, fun q' => ?_⟩ _ _
    fun q => ?_
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q') = π (r q) := Quotient.exact h
    obtain ⟨g, hg⟩ := h2 g' _ _ hg
    rw [← hr q, ← hr q']
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨d, hd⟩ := hs (r' q')
    refine ⟨Quotient.mk _ d, ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g • d = r (Quotient.mk _ d) := Quotient.exact (hr (Quotient.mk _ d))
    obtain ⟨g', hg'⟩ := h1 g d
    rw [← hr' q', ← hd]
    exact Quotient.sound ⟨g', by rw [← hg, hg']⟩
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q) = r' (Quotient.mk _ (π (r q))) := Quotient.exact (hr' (Quotient.mk _ (π (r q))))
    rw [← hg, hf, h3, Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G') (a := π (r q)) (b := g' • π (r q)) (g := g') rfl).toEquiv]

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R) (hI : I.Ok)

abbrev PtKer : Type := ∀ i b b', (I.S i).D b → (I.S (i + 1)).D b' → (VV K (lamT hc i) →ₗ[K] VV K (lamT hc (i + 1)))

abbrev ev (i : ℕ) : VV K (lamT hc i) →ₛₗ[σ] (Fr emb σ (R.N i) → ℂ) :=
  evV emb (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) E) (lamT hc i) σ

variable {I hc} (k : PtKer I hc)

def EqTarget (i : ℕ) : Prop := ∀ b b' (g' : (I.S (i + 1)).G b') d d',
  k i b b' d (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' ∘ₗ k i b b' d d'

def ReadsAt (i : ℕ) : Prop := ∀ c c' F, (I.chain emb σ hI hc).Kmap i c c' (ev emb σ hc i F) =
  ev emb σ hc (i + 1) (k i c.1 c'.1 ((I.S i).rep c) ((I.S (i + 1)).rep c') F)

def stepPt (i : ℕ) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β) (d' : (I.S (i + 1)).D b') : VV K (lamT hc (i + 1)) :=
  letI := I.clFin hI i
  ∑ c : (I.S i).Cl, ((Nat.card ((I.S i).Stab c) : ℕ) : K)⁻¹ • k i c.1 b' ((I.S i).rep c) d' (x c)

def colPt (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (j : ℕ) : ∀ b, (I.S j).D b → VV K (lamT hc j) :=
  Nat.rec (motive := fun j => ∀ b, (I.S j).D b → VV K (lamT hc j)) φ
    (fun j ψ => stepPt hI k j fun c => ψ c.1 ((I.S j).rep c)) j

variable {emb k}

theorem stepPt_smul {i : ℕ} (h : EqTarget emb k i) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β)
    (g' : (I.S (i + 1)).G b') (d' : (I.S (i + 1)).D b') :
    stepPt hI k i x b' (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' (stepPt hI k i x b' d') := by
  unfold stepPt

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h, map_smul]
  rfl

theorem colPt_smul (h : ∀ i, i < R.m → EqTarget emb k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (h0 : 0 < j) (hj : j ≤ R.m)
    (b : (I.S j).β) (g : (I.S j).G b) (d : (I.S j).D b) :
    colPt hI k φ j b (g • d) = (I.S j).rho emb (lamT hc j) b g (colPt hI k φ j b d) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact stepPt_smul hI (h i (by omega)) _ b g d

variable {σ hI}

theorem K_ev {i : ℕ} (h : ReadsAt emb σ hI k i) (x : (I.S i).Cl → VV K (lamT hc i)) :
    (I.chain emb σ hI hc).K i (fun c => ev emb σ hc i (x c)) =
      fun c' => ev emb σ hc (i + 1) (stepPt hI k i x c'.1 ((I.S (i + 1)).rep c')) := by
  funext c'
  unfold stepPt

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smulₛₗ, map_inv₀, map_natCast, ← h]
  rfl

theorem chain_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (hj : j ≤ R.m) :
    letI := (I.chain emb σ hI hc).clsFin
    Formalism.ThetaLiftIndependence.chainOpM (I.chain emb σ hI hc).wt (I.chain emb σ hI hc).Kmap j (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) =
      fun c => ev emb σ hc j (colPt hI k φ j c.1 ((I.S j).rep c)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine Eq.trans ?_ (K_ev (h j (by omega)) fun c => colPt hI k φ j c.1 ((I.S j).rep c))
    rw [← ih (by omega)]
    rfl

theorem exists_K_embF {i : ℕ} (h : ReadsAt emb σ hI k i) (h' : EqTarget emb k i) (hF : ((I.S i).fam emb (lamT hc i)).Ok)
    (hF' : ((I.S (i + 1)).fam emb (lamT hc (i + 1))).Ok) (x : (I.S i).FormsK emb (lamT hc i) hF) :
    ∃ y, (I.S (i + 1)).embF emb σ (lamT hc (i + 1)) hF' y = (I.chain emb σ hI hc).K i ((I.S i).embF emb σ (lamT hc i) hF x) :=
  ⟨⟨fun c' => stepPt hI k i x.1 c'.1 ((I.S (i + 1)).rep c'), fun c' g =>
    (stepPt_smul hI h' x.1 c'.1 g.1 _).symm.trans (congrArg (stepPt hI k i x.1 c'.1) g.2)⟩, (K_ev h x.1).symm⟩

variable (Q : PerIn I) (hQ : Q.Ok)

theorem lower_ev (x : (I.S R.m).Cl → VV K (lamT hc R.m)) (c : Q.S'.Cl) :
    (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz fun c => ev emb σ hc R.m (x c)) c =
      evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
          ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x (Q.tilC c)))) := by
  show fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x (Q.tilC c)))))) = _
  rw [← LvT.BuiltChain.evV_rho, LvT.BuiltChain.polOf_evV, LvT.BuiltChain.br_map]
  rfl

theorem exists_lower_embF (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ))
    (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ)) (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) :
    ∃ y, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, funext fun c => (lower_ev Q hQ x.1 c).symm⟩
  have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
      (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
  have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
    have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    exact h3
  show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
  rw [← LvT.BuiltChain.brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
    (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
    (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
  exact congrArg B h2

theorem ptilCol_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (h' : ∀ i, i < R.m → EqTarget emb k i)
    (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (F : Q.Mt emb σ) (y : Q.S'.Cl → VV K Q.sgT)
    (hy : ∀ c, Q.rd emb σ F c = MvPolynomial.map σ (y c).1) :
    (Q.per emb σ hI hQ hc).PtilCol (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) F = letI := Q.clFin hQ
      σ (∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : K)⁻¹ • pairBK Q.sgT
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) (colPt hI k φ R.m Q.b0 (Q.tilPt c))) (y c)) := by
  unfold PeriodMap.PtilCol PeriodMap.Ptil ColumnChain.col
  rw [chain_ev h φ le_rfl]
  have e := funext (lower_ev (σ := σ) (emb := emb) (hI := hI) Q hQ fun c => colPt hI k φ R.m c.1 ((I.S R.m).rep c))
  refine (congrArg (fun z => (Q.per emb σ hI hQ hc).period z F) e).trans ?_

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  have e2 := colPt_smul hI h' φ (lt_of_lt_of_le (by norm_num) R.two_le_m) le_rfl Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
    ((I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c)))
  rw [GStep.mv_smul] at e2
  rw [pairBK_apply, PeriodOnStep.map_pairB, ← hy, ← PeriodOnStep.polOf_evV σ emb, e2]
  rfl

end GlobalTheory.Mem.Col2.KerRat
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdComp

theorem eq_zero_of_valued_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (x : P.adicCompletion E) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
  have h1 := h (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_eps_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) : adAt F w (afsplitEps E v) = 1 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 1))
    (fun n => by
      rw [he]
      exact hspec _ 1 w n (by rw [h, afsplitI_self, map_one, sub_self, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_one, map_one] at h0
  exact h0

theorem adAt_eps_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) : adAt F w (afsplitEps E v) = 0 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 0))
    (fun n => by
      rw [he]
      exact hspec _ 0 w n (by rw [afsplitI_ne v _ h, map_zero, sub_zero, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_zero, map_zero] at h0
  exact h0

theorem adAt_eps_mul_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = adAt F w z := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_under v w h, one_mul]

theorem adAt_eps_mul_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = 0 := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_ne v w h, zero_mul]

theorem prV_zero_int_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  intro F E _ _ _ _ _ v z
  classical
  have hinj : ∀ x y : E ⊗[F] v.adicCompletion F, afsplitIE v x = afsplitIE v y → x = y := by
    intro x y hxy
    rw [← afsplit_prV_IE v x, hxy, afsplit_prV_IE]
  have hdec : afsplitIE v (prV (E := E) v z) = afsplitEps E v * z := afsplit_decomp v z
  have hz : ∀ w : HeightOneSpectrum (𝓞 E), adAt F w (0 : AfE F E) = 0 := by
    intro w; unfold adAt; exact map_zero _
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 E),
      adAt F w (afsplitEps E v * z) = if w.under (𝓞 F) = v then adAt F w z else 0 := by
    intro w
    split_ifs with hw
    · exact adAt_eps_mul_of_under v w hw z
    · exact adAt_eps_mul_of_ne v w hw z
  refine ⟨⟨fun h0 w hw => ?_, fun h => ?_⟩, ⟨fun hint w hw => ?_, fun h => ?_⟩⟩
  · rw [← adAt_eps_mul_of_under v w hw z, ← hdec, h0, map_zero, hz]
  · apply hinj
    rw [hdec, map_zero]
    apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [hcomp, hz]
    split_ifs with hw
    · exact h w hw
    · rfl
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [← hdec]; exact afsplit_IE_int v _ hint
    rw [← adAt_eps_mul_of_under v w hw z]
    exact (mem_rInt_iff F E _).mp h1 w
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [mem_rInt_iff]
      intro w
      change Valued.v (adAt F w (afsplitEps E v * z)) ≤ 1
      rw [hcomp]
      split_ifs with hw
      · exact h w hw
      · rw [map_zero]; exact zero_le'
    have h2 := afsplit_prV_int v _ h1
    rwa [← hdec, afsplit_prV_IE] at h2

end GlobalTheory.Mem.Col2.AdComp
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}


omit [NumberField E] [StarRing E] in
theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]


omit [NumberField E] [StarRing E] in
theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  have hspan : Submodule.span E (p.deco.1.N : Set (Sp E n)) = ⊤ := by
    let L := p.deco.1.N
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let f : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    have hu : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) L := p.deco.2.uni
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr p.deco.2.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) hspan]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG (E := E) (n := n) (SG := SG)) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp

    rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.L2
open Formalism.AUTREP (GAf)

theorem _root_.GlobalTheory.T.relIndex_stabilizer_eq_local_relIndex : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (J : Subgroup (GAf L n)) (H : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))), (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ s.loc n κ ∈ H)) → J.relIndex (GlobalTheory.HeckeScalarSph.locK n s.v) = H.relIndex (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) := by
  first | exact @GlobalTheory.LocRelIndex.main | exact GlobalTheory.LocRelIndex.main | (intros; apply GlobalTheory.LocRelIndex.main <;> assumption)
end
