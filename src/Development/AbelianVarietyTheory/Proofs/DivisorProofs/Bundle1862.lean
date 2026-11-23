module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermEqOfSimilitudeRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (g : ℕ) (X : Data D.host.E W.rank) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin W.rank) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (he : Even V.rank), V.gram = 1 → IsMod W rfl X → IsSympl X bas → ∃ (X' : Data D.host.E W.rank) (m : GlobalTheory.Ker.Match V W X') (hq' : X'.p0 + X.p0 = W.rank) (hq : X.p0 + X'.p0 = W.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin W.rank) (hs : IsSympl X' bas'), X'.Λ = X.Λ ∧ (∀ a, (bas' a : Fin W.rank → D.host.E) = bas a) ∧ (∀ u v, EF X' u v = EF X u v) ∧ (∀ (y : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (φ : TF V.rank g), heisG X' bas' y φ = heisG X bas y φ) ∧ (∀ j (a : Fin W.rank) (k : Fin X'.p0 ⊕ Fin X.p0), (idx j).2 = rowIdx hq k → ((idx' j).2 : ℕ) = Sum.elim (fun i : Fin X'.p0 => (i : ℕ)) (fun i : Fin X.p0 => X'.p0 + (i : ℕ)) k) ∧ (∀ j, (idx' j).1.1 = ComplexEmbedding.conjugate (idx j).1.1) ∧ ∀ x : Frame X.Ψ W.rank, IsONFr X x → (∃ B, IsBasOf W rfl X hq x B) ∧ ∀ B, IsBasOf W rfl X hq x B → let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs, he⟩; C.IsB B ∧ IsInvOf W rfl X x (C.sB B) ∧ (∀ s, IsInvOf W rfl X x s → s = C.sB B) ∧ (∀ w, C.zOf (C.xB B) w = zOf θ V W rfl X idx x w) ∧ (∀ v, pv X' idx' (C.xB B) v = pv X idx x v) ∧ (∀ z z', hx X' bas' idx' (C.xB B) z z' = hx X bas idx x z z') ∧ (∀ φ : TF V.rank g, thA X' bas' idx' φ (C.xB B) = thA X bas idx φ x) ∧ (∀ u : GA D W, IsONFr X (frMove θ W rfl X u x) ∧ IsBasOf W rfl X hq (frMove θ W rfl X u x) (C.mvB u B)) ∧ ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ → ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB B) φ) := by
  first | exact @GlobalTheory.AdTh.reads_iff_eq_th | exact GlobalTheory.AdTh.reads_iff_eq_th | (intros; apply GlobalTheory.AdTh.reads_iff_eq_th <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twisted_orbital_integral_levi_constant_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w (n := n)) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w (n := n)) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  first | exact @GlobalTheory.LeviDesc.orbInt_descent | exact GlobalTheory.LeviDesc.orbInt_descent | (intros; apply GlobalTheory.LeviDesc.orbInt_descent <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank), IsONFr X x → IsInvOf W hr X x s → IsBasOf W hr X hq x BW → IsVarOf V W X q0 vr → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ), P.IsHomogeneous d → pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) BW f (MvPolynomial.rename vr P) 0 = ((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P x := by
  first | exact @GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP | exact GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP | (intros; apply GlobalTheory.AdTh.Fock.pureTensorO_zero_eq_thP <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral



theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime
  have lemCC := GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.term_eq_of_similitude_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → P.Rel Q → Q.term Kf f r K φ = P.term Kf f r K φ := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_of_rel) | (exact GlobalTheory.LKMid.Pair.term_eq_of_rel) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_of_rel <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  first | exact @GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction | exact GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction | (intros; apply GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction <;> assumption)
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis | exact GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis | (intros; apply GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis <;> assumption)
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem defNode_isV {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (X : Node) (hX : DefNode D.R.m X) : (G.node X).IsV (X.rank D) 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    rcases i with _ | i
    · have h := colY_isV D T L μ0 hL D.R.m le_rfl
      rw [Nat.sub_self, Nat.zero_div] at h
      exact h
    · have h := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
      simp only [Node.neg, Nat.sub_self, Nat.zero_div] at h
      exact h
  · exact absurd hX id
  · exact G.isV (X := .top j) hX (fun j' h => by cases h)

theorem unrIdem_mul {D : D7} {a b : (AE D)ˣ →* Circle} {e : AE D} (ha : UnrIdem a e) (hb : UnrIdem b e) :
    UnrIdem (a * b) e := fun x h1 h2 h3 => by
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem off_mono {D : D7} {S S' : Finset ℕ} (h : S ⊆ S') {w : Pl D.host.E} (hw : Off S' w) : Off S w :=
  fun q hq => hw q (h hq)



theorem exists_std {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (U : Set T) (hU : U.Finite) : Nonempty (Std G U) := by
  classical
  obtain ⟨S₁, hS₁p, hS₁⟩ := GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces D T L sc G U hU
  have key : ∀ c : (AE D)ˣ →* Circle, ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (Continuous c → ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e) := fun c => by
    by_cases hc : Continuous c
    · obtain ⟨S, h1, h2⟩ := GlobalTheory.T.character_unramified_off_finite_primes D c hc
      exact ⟨S, h1, fun _ => h2⟩
    · exact ⟨∅, by simp, fun h => absurd h hc⟩
  choose Sc hScp hSc using key
  set S : Finset ℕ := S₁ ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => Sc (L.mu0 j)) ∪
    hU.toFinset.biUnion (fun t => Sc (L.xi t)) with hSdef
  have hSp : ∀ q ∈ S, q.Prime := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion] at hq
    rcases hq with (hq | ⟨j, -, hq⟩) | ⟨t, -, hq⟩
    · exact hS₁p q hq
    · exact hScp _ q hq
    · exact hScp _ q hq
  have hsub1 : S₁ ⊆ S := fun q hq => by simp [hSdef, hq]
  have hsubμ : ∀ j, j ≤ D.R.m → Sc (L.mu0 j) ⊆ S := fun j hj q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
    exact Or.inl (Or.inr ⟨j, by omega, hq⟩)
  have hsubξ : ∀ t ∈ U, Sc (L.xi t) ⊆ S := fun t ht q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    exact Or.inr ⟨t, ht, hq⟩
  have hcμ : ∀ j, 1 ≤ j → j ≤ D.R.m → Continuous (L.mu0 j) := fun j h1 h2 => by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (hL.mu0 ⟨k, by omega⟩).1.1
  have hV : ∀ X, DefNode D.R.m X → ∃ (fr : GL (Fin (G.V X).rank) D.host.E) (u : FinPt G X),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V X).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V X) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X) := by
    intro X hX
    have h := defNode_isV G μ0 hL X hX
    exact GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint D (G.V X) (G.Λ X) h.sigOK (fun τ => by rw [h.sig τ, h.rank, Nat.sub_zero]) h.sd S hSp
  choose fr0 u0 h0 using hV
  have hmm : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  obtain ⟨frT, uT, hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩ :=
    GlobalTheory.T.gridTopVertex_frame_point_transport_lattice D T L sc G S (fr0 _ hmm) (u0 _ hmm) (h0 _ hmm).1 (h0 _ hmm).2.1 (h0 _ hmm).2.2
  have hne : (Node.grid D.R.m D.R.m) ≠ Node.top D.R.m := fun h => by cases h
  obtain ⟨fr, frt, hfr⟩ : ∃ fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E, fr (.top D.R.m) = frT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → fr X = fr0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then fr0 X h else 1) (.top D.R.m) frT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  obtain ⟨u, ut, hu⟩ : ∃ u : ∀ X : Node, FinPt G X, u (.top D.R.m) = uT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → u X = u0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then u0 X h else 1) (.top D.R.m) uT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  have frmm := hfr _ hmm hne
  have hu_mm := hu _ hmm hne
  refine ⟨⟨S, hSp, ?_, ?_, fr, ?_, u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun w hw => hS₁ w (off_mono hsub1 hw)
  · intro w hw e he t ht j h1 h2
    exact unrIdem_mul (hSc _ (hcμ j h1 h2) w (off_mono (hsubμ j h2) hw) e he)
      (hSc _ (hL.xi t).1.1 w (off_mono (hsubξ t ht) hw) e he)
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt]; exact hT1
    · have := hfr X hX hXt
      rw [this]; exact (h0 X hX).1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [ut]; exact hT2
    · have := hu X hX hXt
      rw [this]; exact (h0 X hX).2.1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt, ut]; exact hT3
    · have e1 := hfr X hX hXt
      have e2 := hu X hX hXt
      rw [e1, e2]; exact (h0 X hX).2.2
  · intro i k; rw [frt, frmm]; exact hT4 i k
  · intro i; rw [frt]; exact hT5 i
  · rw [ut, hu_mm]; exact hT6
  · rw [ut]; exact hT7

end GlobalTheory.FunObj
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem sum_inner_integral_eq {X U ι : Type} [MeasurableSpace X] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] [Fintype ι] (ν : Measure X) (f : X → ℂ) (ρ : X → U →L[ℂ] U) (e : ι → U) (T : U →L[ℂ] U)
    (h : ∀ v, Integrable (fun x => f x • ρ x v) ν ∧ T v = ∫ x, f x • ρ x v ∂ν) :
    ∑ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, f x * ∑ j, ⟪e j, ρ x (e j)⟫_ℂ ∂ν := by
  have h1 : ∀ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, ⟪e j, f x • ρ x (e j)⟫_ℂ ∂ν := fun j => by
    rw [(h (e j)).2, integral_inner (h (e j)).1]
  simp only [h1]
  rw [← integral_finsetSum _ fun j _ => (h (e j)).1.const_inner (e j)]
  simp only [inner_smul_right, Finset.mul_sum]

theorem stTr_of_range_steps (hF : UFin) (hS : RangeShape) (hK : RangeK) (hT : TraceSum) : StTr := by
  intro n ε μ _ U _ _ _ π hπ hirr d
  obtain ⟨L, hL, hmem, -⟩ := hF n ε U π hπ hirr d
  refine ⟨fun g => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π g (stdOrthonormalBasis ℂ L j : U)⟫_ℂ, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)
  · intro φ hφ
    obtain ⟨hop, hr⟩ := hS n ε μ U π hπ d φ hφ
    have := hT U L _ fun u => hmem _ (hr u).1
    rwa [sum_inner_integral_eq μ (fun g => φ (toM g)) (fun g => π g) _ _ hop] at this
  · intro P hP
    obtain ⟨B, hB, hr⟩ := hK n ε U π hπ P
    refine ⟨B, fun v => (hB v).2, ?_⟩
    have := hT U L B fun u => hmem _ fun l => by
      obtain ⟨Q, hQ, hQ'⟩ := hr u l
      exact ⟨Q, hQ.trans hP, hQ'⟩
    rwa [sum_inner_integral_eq (muK ε) (fun k : KG ε => ev (toMK k) P) (fun k : KG ε => π k) _ _ hB] at this

theorem stTr : StTr := stTr_of_range_steps GlobalTheory.T.polyCoeff_vectors_lie_in_finiteDimensional_smooth GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial rangeK GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le

end GlobalTheory.PsCo.Pc3

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  first | exact @GlobalTheory.LocFinU.locFin | exact GlobalTheory.LocFinU.locFin | (intros; apply GlobalTheory.LocFinU.locFin <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | exact GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | (intros; apply GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert <;> assumption)
end
