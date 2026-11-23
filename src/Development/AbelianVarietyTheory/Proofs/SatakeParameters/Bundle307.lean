module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle460
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Adelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle298
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle299
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.kernelDegrees_small_against_typePrimes : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  first | exact @GlobalTheory.AtG.KernelSizes.sizeAt_of_params | exact GlobalTheory.AtG.KernelSizes.sizeAt_of_params | (intros; apply GlobalTheory.AtG.KernelSizes.sizeAt_of_params <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem tuple_kernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z →
    ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  intro B X I h _ l Z l0 Tw hJ hTw u a j hj
  subst hTw
  exact ((KerRat.kernels_rational I l Z h hJ
    (Or.inr (GlobalTheory.Core.Ht2.family_laws I h (base_fields_primes_ok B X).1 l Z))).2.2 l0 u a).1 j hj

end GlobalTheory.TwU.AtTrue
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem kerField_le_rec :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hS y
  obtain ⟨hX, hseam⟩ := And.intro hS.X_eq hS.seam
  clear hS
  cases t
  dsimp only at hX hseam y ⊢
  subst hX
  have h := eq_of_heq hseam
  subst h
  exact ⟨y, rfl⟩

end GlobalTheory.TwU
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.UnderQp

theorem mem_QE_of_heq {B : Base} {X : PreX B.toPre} (I : TC B X) {Xf : Fields} (hX : Xf = B.fields) {S : Set ℕ} (hS : S = I.S)
    {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} (hsel : HEq sel I.sel)
    {tup : I.ι → Tup Xf.F Xf.E Xf.K S} (htup : HEq tup I.tup) (a : I.ι) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hP : P ∈ I.Q a) (q : ℕ) (hq : (q : 𝓞 B.fields.E) ∈ P.asIdeal) :
    ∃ P' ∈ QE sel (tup a : Chr Xf.F Xf.E Xf.K), (q : 𝓞 Xf.E) ∈ P'.asIdeal := by
  subst hX
  subst hS
  cases hsel
  cases htup
  exact ⟨P, hP, hq⟩

theorem underQ_qp : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), I.UnderQ a v → ∃ q ∈ Y.Qp a, ((q : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hSK a v hv
  obtain ⟨P, hP, hPv⟩ := hv
  have hN1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  set q := (Ideal.absNorm P.asIdeal).minFac with hqdef
  have hqp : q.Prime := Nat.minFac_prime hN1
  have hqP : (q : 𝓞 B.fields.E) ∈ P.asIdeal :=
    GlobalTheory.KerTie.natCast_mem_of_prime_dvd_absNorm P hqp (Nat.minFac_dvd _)
  refine ⟨q, ?_, ?_⟩
  · exact (t.Q_rec a q).2 ⟨hqp, mem_QE_of_heq I hSK.X_eq hSK.S hSK.sel hSK.tup a P hP q hqP⟩
  · rw [← hPv]
    show (q : 𝓞 B.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 B.host.F) (𝓞 B.host.E))
    rw [Ideal.mem_comap, map_natCast]
    exact hqP

end GlobalTheory.TwU.UnderQp
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntTied_true_ent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.ent = E ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  obtain ⟨t, ht, hO, -, hTop⟩ := GlobalTheory.T.kernelEntries_compatible_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex O E hQ hStd hU hE hS
  exact kerEntTied_withEnt I l Z O E hE hS t ht hO hTop

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem stepZeroFormIdentification_refTuple_eq_id : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  intro B X I _ _ l Z l0 u
  apply LinearEquiv.ext
  intro x
  have h := (l0 u I.mu0).choose_spec.2 x
  rw [stepZeroTwist_reference_tuple_eq_id l u] at h
  exact (I.fm l u I.mu0).emb_inj 0 h

end GlobalTheory.TwU.AtTrue
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue.Cl


open Classical in
theorem sameCoset_of_mem_cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j)
    (h : j + 1 = R.m) (P : rowSG Pr sel mu) {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z' ∈ cosetIn p P) :
    SameCoset sel mu cst P z z' := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hzw'⟩ := hz'
  obtain ⟨y, -, hY⟩ := p.mem_ybSet h
  rw [hY] at hw hw'
  have hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    have e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw
    have e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw'
    have := sub_mem e1 e2
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := (mem_locLat _ _ _ _).1 hww P
  set F := frsF sel mu p.1.1 P with hF
  set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc
  have hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c := by
    rw [hc]; split_ifs <;> simp
  simp only [hc'] at h1
  have hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
    intro x
    rw [hF]
    unfold frsF
    split_ifs with hP
    · exact (Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x
    · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x
  have h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1 := by
    rw [← map_sub, ← map_smul]
    apply (hFm _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h1
  have h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w') := by
    rw [← smul_sub, ← smul_add]
    congr 1
    abel
  have h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1 := by
    rw [h3]
    exact add_mem (sub_mem hzw hzw') h2
  intro l
  have h5 := (ciMem_stdAt _ _).1 h4 l
  rw [Pi.smul_apply, smul_eq_mul] at h5
  exact h5

end GlobalTheory.TwU.AtTrue.Cl

namespace GlobalTheory.TwU.AtTrue.Cl

end GlobalTheory.TwU.AtTrue.Cl
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.StepZeroChr

theorem isPtOf_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩



theorem chr_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  intro B X I hI hP l Z u a Lb U chi y st k hR c κ0 c' hc' _ hchi x κ hκ hpt
  have hd : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    subst hc'
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  have hΛ := ClsZero.levelTypePrimes_stepZero_eq_colLev hI a c'.1
  have hΛ0 := ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 c.1
  have hm : κ.2.1.1 ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
    rw [hΛ0, ← hΛ]
    exact κ.2.1.2
  let κ' : (I.stp u I.mu0 0).G c.1 := (κ.1, ⟨κ.2.1.1, hm⟩, 1)
  have e1 : ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1.deco =
      ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1.deco := by
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep c).1.1.deco = ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep c').1.1.deco
    rw [hd]
  have h1 : PtOf (y c * (κ0 * x).1 * k) ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1 := by
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact isPtOf_of_deco (RefTup.twistPrimes_reference_tuple_eq_empty B X I) e1 hpt
  have h2 := hR.chr c (κ0 * x) κ' hκ h1
  rw [map_mul, hchi, one_mul] at h2
  refine h2.trans ?_
  congr 2
  show (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr ⟨κ.2.1.1, hm⟩ *
      (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr 1 =
    (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.2
  rw [map_one, StepZero.chr_eq_one (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a c'.1), StepZero.chr_congr hΛ, StepZero.chr_congr hΛ0]

end GlobalTheory.TwU.StepZeroChr
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.StabZero

open GlobalTheory.Mem.Col2.ClsZero

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem idx_empty (a : I.ι) (u : B.Word) {b : (I.stp u a 0).β} (p : (I.stp u a 0).D b) : p.1.2 = ∅ := by
  obtain ⟨⟨q, Y⟩, hY⟩ := p
  rw [ys0 a] at hY
  exact hY

theorem gam_eq_one (h : I.Ok) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1)
    (c : (I.stp u a 0).Cl) (s : (I.stp u a 0).Stab c) : s.1.1 = 1 := by
  obtain ⟨b⟩ := stepZero_chartIndex_nonempty h a
  obtain ⟨c', rfl⟩ := (bij0 h u a b).2 c
  have hd := stepZero_corresponding_representatives_same_deco h u a b c'
  set p := (I.stp u a 0).rep (I.cl0 u a b c') with hp
  set p0 := (I.stp u I.mu0 0).rep c' with hp0
  have hs : _ = _ := s.2
  have hsd : ((s.1.1, (s.1.2.1.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco :=
    congrArg (fun x => DecoF.deco x.1.1) hs
  rw [hd] at hsd
  have hγ : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (z : Sp B.fields.E (B.R.N 0)),
      s.1.1.1 z ∈ p0.1.1.deco.1.at P ↔ z ∈ p0.1.1.deco.1.at P := by
    intro P z
    have e := congrArg (fun d : DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := (B.primes X).vT u) (SG := (B.primes X).vGs) => s.1.1.1 z ∈ d.1.at P) hsd
    simp only at e
    rw [← e]
    show s.1.1.1 z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap s.1.1.1 _) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
  have hc : ∀ P, ((p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P)) ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    show (p0.1.1.1.2 P).symm (s.1.1.1 (p0.1.1.1.2 P x)) ∈ stdAt _ _ P.1 ↔ x ∈ stdAt _ _ P.1
    rw [← p0.1.1.2 P, LinearEquiv.apply_symm_apply, ← p0.1.1.2 P x]
    exact hγ P.1 _
  let t : (I.stp u I.mu0 0).G c'.1 :=
    (s.1.1, ⟨s.1.2.1.1, by
      have e1 := levelTypePrimes_stepZero_eq_colLev h I.mu0 c'.1
      have e2 := levelTypePrimes_stepZero_eq_colLev h a b
      rw [e1, ← e2]
      exact s.1.2.1.2⟩,
     ⟨fun P => ⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩, by
      rw [chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 c'.1]
      intro P _
      trivial⟩)
  let st : (I.stp u I.mu0 0).Stab c' := ⟨t, by
    show _ = _
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hsd ?_)) ?_)
    · funext P
      show s.1.1.1 * p0.1.1.1.2 P * (⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩⁻¹ : ↥(GLint B.fields.E (B.R.N 0) P.1)).1 = p0.1.1.1.2 P
      simp only [Subgroup.coe_inv]
      group
    · show (fun v => s.1.1.1 v) '' p0.1.2 = p0.1.2
      rw [idx_empty I.mu0 u p0, Set.image_empty]⟩
  have hsub := (Nat.card_eq_one_iff_unique.1 (hm c')).1
  have e : st = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : (I.stp u I.mu0 0).Stab c' => x.1.1) e

theorem card_stab_zero (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1) (c : (I.stp u a 0).Cl) :
    Nat.card ((I.stp u a 0).Stab c) = 1 := by
  have e : ∀ s : (I.stp u a 0).Stab c, s = 1 := fun s =>
    Subtype.ext (((l.ch u a).step 0).stab_inj c.1 s.1 _ s.2 (by
      change (ufGL _ _) s.1.1 = 1
      rw [gam_eq_one h u a hm c s, map_one]))
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => (e s).trans (e s').symm⟩, ⟨1⟩⟩

end GlobalTheory.Pdv.StabZero

namespace GlobalTheory.Pdv

open GlobalTheory.Pdv.StabZero

theorem stepZero_trivial_stabilisers_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  intro B X I h _ l Z lev
  exact ⟨Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev,
    fun u μ _ c => card_stab_zero h l u μ (fun c' => Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev u c') c⟩

end GlobalTheory.Pdv

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.pairKernelLaw_of_finiteDatumLaw : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  first | exact @GlobalTheory.KFiDat.termLaw_of_xi | exact GlobalTheory.KFiDat.termLaw_of_xi | (intros; apply GlobalTheory.KFiDat.termLaw_of_xi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), _root_.Formalism.DivisionValues.conjPl P ≠ P → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (d : List ℤ), ∃ a ∈ Algebra.adjoin ℂ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨ x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∀ u : M, (∀ k ∈ hyp V P, π k u = u) → a u = opOf π P (Finsupp.single d 1) u := by
  first | exact @GlobalTheory.SplitGen.gen_split | exact GlobalTheory.SplitGen.gen_split | (intros; apply GlobalTheory.SplitGen.gen_split <;> assumption)
end
