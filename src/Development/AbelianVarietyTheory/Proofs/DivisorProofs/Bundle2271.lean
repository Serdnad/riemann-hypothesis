module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle004
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IntLift

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.UnitaryMove (ct blockUnit)

theorem adjugate_mem {A : Type} [CommRing A] (O : Subring A) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (i j : Fin n) : N.adjugate i j ∈ O := by
  let M : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e : N = O.subtype.mapMatrix M := rfl
  rw [e, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

theorem exists_block {A : Type} [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a) (O : Subring A) (hO : ∀ a ∈ O, c a ∈ O)
    {ε w : A} (h1 : ε * ε = ε) (h2 : ε * c ε = 0) (hε : ε ∈ O) (hw : w ∈ O) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (hd : ε * (w * N.det) = ε) :
    ∃ K K' : Matrix (Fin n) (Fin n) A, K * K' = 1 ∧ K' * K = 1 ∧ ct c K = K' ∧ (∀ i j, K i j ∈ O ∧ K' i j ∈ O) ∧
      ∀ i j, ε * K' i j = ε * N i j := by
  have hP : ∀ i j, (w • N.adjugate) i j ∈ O := fun i j => mul_mem hw (adjugate_mem O N hN i j)
  have hPQ : ε • ((w • N.adjugate) * N) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_assoc, hd]
  have hQP : ε • (N * (w • N.adjugate)) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul, mul_assoc, hd]
  generalize w • N.adjugate = P at hP hPQ hQP
  obtain ⟨a, b, d⟩ := blockUnit c hc h1 h2 P N hPQ hQP
  have hf : 1 - ε - c ε ∈ O := sub_mem (sub_mem (one_mem _) hε) (hO _ hε)
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) A) i j ∈ O := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨_, _, a, b, d, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hP i j))) (mul_mem (hO _ hε) (hO _ (hN j i)))
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hN i j))) (mul_mem (hO _ hε) (hO _ (hP j i)))
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (N i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h1 +
      (ct c P i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h2

theorem toE_injective (D : D7) : Function.Injective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective.comp (GlobalTheory.BotFormula.toAfE D).injective

theorem exists_lift : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  intro D e SS he a N hN x hx
  obtain ⟨-, hx1, hx2⟩ := hx
  have hdet : (N.map (toE D)).det = toE D N.det := (RingHom.map_det (toE D) _).symm
  have h1 := CharVal.eps_idem he
  have hxe : finQ D (x : AE D) = 1 - finQ D e + finQ D e * N.det := toE_injective D (by
    rw [CharVal.toE_finQ, hx1, hdet, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, CharVal.toE_finQ])
  have hxx : finQ D (x : AE D) * finQ D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hd : finQ D e * (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * N.det) = finQ D e := by
    rw [hxe] at hxx
    linear_combination finQ D e * hxx + (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * (1 - N.det)) * h1
  obtain ⟨K, K', a1, a2, a3, a4, a5⟩ := exists_block (Formalism.MainNotions.StandardLatticesGL3.sgA D) (GlobalTheory.NormSum.VacMove.sgA_sgA D) (OhE D)
    (fun _ h => GlobalTheory.NormSum.VacMove.sgA_mem D h) h1 (CharVal.eps_conj he) (CharVal.eps_int he) (CharVal.finQ_int hx2) N hN hd
  let u : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ⟨K, K', a1, a2⟩
  have hu : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D a := by
    change Formalism.UG.cT _ K * _ * K = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact (congrArg (· * K) a3).trans a2
  exact ⟨⟨u, hu⟩, (GlobalTheory.NormSum.mem_intG _).2 a4, a5⟩

end GlobalTheory.StdRead.IntLift

end
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IdealDict

open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem toE_bijective (D : D7) : Function.Bijective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective

theorem toE_inc (b : 𝓞 D.host.E) :
    toE D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  rw [← finQ_incA, toE_finQ]
  rfl

theorem inId_of_mem {𝔪 : Ideal (𝓞 D.host.E)} {y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hy : y ∈ hatId D 𝔪) : InId 𝔪 (toE D y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    have ht' := (toE_int_iff t).2 ht
    have h := Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _
      (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
    rw [RingHom.map_mul, toE_inc]
    exact ⟨_, h⟩
  | zero => rw [RingHom.map_zero]; exact ⟨zero_mem _, Ideal.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    rw [RingHom.map_add (f := _)]
    exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    rw [RingHom.map_neg]
    exact ⟨neg_mem h1, Submodule.neg_mem _ h2⟩

theorem exists_of_mem_idS {𝔪 : Ideal (𝓞 D.host.E)} {u : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hu : u ∈ Ideal.map (Formalism.L2.DIV.oToS D.host.F D.host.E) 𝔪) : ∃ y ∈ hatId D 𝔪, toE D y = u.1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩
  | zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [RingHom.map_add (f := _), e, e']
    exact (AddMemClass.coe_add _ a b).symm
  | smul s a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨t, ht⟩ := (toE_bijective D).2 s.1
    have htO : t ∈ OhE D := (toE_int_iff t).1 (by rw [ht]; exact s.2)
    refine ⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩
    have h1 := (toE D).map_mul t y
    rw [e, ht] at h1
    rw [smul_eq_mul]
    exact h1.trans (MulMemClass.coe_mul _ s a).symm

theorem inId_toE_iff : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  intro D 𝔪 y
  refine ⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩
  obtain ⟨z, hz, e⟩ := exists_of_mem_idS hm
  rwa [← (toE_bijective D).1 e]

end GlobalTheory.StdRead.IdealDict

end
end

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.integral_action_unit_character_eigen : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 →
  ∀ ν : (AE D)ˣ →* Circle, HasFinPart ν⁻¹ P.W.chV' P.W.ep' → KillsCong ν 𝔪 →
  ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a, k ∈ intG D P.a → P.W.Om k 1 P.e0 = unitChar ν e (matE k) • P.e0 := by
  first | exact @GlobalTheory.StdRead.CharVal.om_vac_eq | exact GlobalTheory.StdRead.CharVal.om_vac_eq | (intros; apply GlobalTheory.StdRead.CharVal.om_vac_eq <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.vert_jac_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h K _ _ z hz P₀ P hU hzP hPG hB w zw hzw hw hzw'
  have key : ∀ b σ', (N σ').map (ev (zw b) W (hzw b)) = GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
      ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
    intro b σ'
    have hx : frX (w b) ≫ TF.Y.j = zw b ≫ toBase TF Z := by
      rw [toBase, ← Category.assoc, hzw' b]; exact (TF.X.lies_ptY (w b)).1.symm
    have hUx : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzw b)
    have hk : ⊤ ≤ (zw b ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 (hzw b)
    have hM : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ (TF.X.F.M k).U := TF.X.F.inM hk (Category.assoc _ _ _)
    obtain ⟨B, hBl, hBu, hBc⟩ := GlobalTheory.T.bigCell_framedPointVectors_lowerTriangular_eigenbasis E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (w b) (zw b) (hzw b)
      _ hx hUx (hzw' b)
    have hF := GlobalTheory.T.framedPointVectors_verticalDeformation_eigenbasis E H Dw l Xo c TF U n e v hv K P₀ P hU _ hPG hB (Pi.single b.toF (1 : K)) (w b) _ hx hUx
      (TF.X.F.M k).toMChart hM (hw b)
    have eq : B σ' * (L σ').map (ev (zw b) W (hzw b)) * (N σ').map (ev (zw b) W (hzw b)) =
        GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
          ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
      refine Matrix.ext fun i j => ?_
      have := GlobalTheory.T.bigCell_eigenbasisCombination_coeff_unique E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (zw b) (hzw b) _ rfl hUx σ' _ _ _
        (hBc σ' i) (hF σ' i)
      have := congrFun this j
      simpa [Matrix.map_mul, Matrix.mul_assoc] using this
    have hN : ∀ i j, j < i → (N σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN1 : ∀ i, (N σ').map (ev (zw b) W (hzw b)) i i = 1 := fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hL : ∀ i j, i < j → (L σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.1 σ' i j hij]
    have hN0 : ∀ i j, j < i → ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i j = 0 :=
      fun i j hij => by simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN01 : ∀ i, ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i i = 1 :=
      fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hbt : ∀ (p q : Fin (Dw.mult σ')), some ⟨σ', (p, q)⟩ = b.toF → p < q := by
      intro p q hpq
      obtain ⟨σb, ⟨⟨i, j⟩, hij⟩⟩ := b
      simp only [GlobalTheory.FlagTan.VIx.toF, Option.some.injEq, Sigma.mk.inj_iff] at hpq
      obtain ⟨rfl, hq⟩ := hpq
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (eq_of_heq hq)
      exact hij
    have hU0 : ∀ i j, j < i → GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i j = 0 := fun i j hij => by
      have h1 : (1 : Matrix (Fin (Dw.mult σ')) (Fin (Dw.mult σ')) K) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, j)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i j hh) (not_lt.2 hij.le)) _
      simp [GlobalTheory.FlagTan.unip, h1, h2]
    have hU1 : ∀ i, GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i i = 1 := fun i => by
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, i)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i i hh) (lt_irrefl _)) _
      simp [GlobalTheory.FlagTan.unip, h2]
    exact GlobalTheory.T.lu_decomposition_unitriangular_unique _ _ _ _ _ _ _ (hBl σ') hL hN hN1 hU0 hU1 hN0 hN01 eq
  refine ⟨?_, fun b r => GlobalTheory.T.derivative_basePullback_eq_zero_along_verticalDeformation E H Dw l Xo c TF Z U.1 W h.2.1 K P _ (w b) (zw b) (hzw b) (hw b) (hzw' b) r⟩
  have hM : ∀ σ i j, j < i → (N σ).map (ev z W hz) i j = 0 := fun σ i j hij => by simp [h.2.2.2.2.2.1 σ i j hij]
  have hM1 : ∀ σ i, (N σ).map (ev z W hz) i i = 1 := fun σ i => by simp [h.2.2.2.2.2.2.1 σ i]
  convert GlobalTheory.T.det_bigCellCoordinateJacobian_verticalChanges_eq_one E H Dw K (fun σ => (N σ).map (ev z W hz)) hM hM1 using 2
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.of_apply, cellCoord]
  rw [← key b a.1]
  rfl
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem derivation_prod_eq_zero_of_forall {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    (D : Derivation F R R) {ι : Type} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 :=
  Finset.prod_induction f (fun y => D y = 0)
    (fun a b ha hb => by rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero])
    (Derivation.map_one_eq_zero D) h

theorem logDet_local_eq_unit_mul_prod :
    ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  intro F A R _ _ _ _ _ _ _ _ _ _ _ _ P _ _ n m x e J hrsp hbs I hI b _hbF hbI hspan
  obtain ⟨bs, hbs⟩ := hbs
  set φ := algebraMap A R with hφ
  set r : Fin m → R := fun j => φ (x (e j)) with hr
  set g : R := ∏ j ∈ J, r j with hg
  have hφg : φ (∏ j ∈ J, x (e j)) = g := by rw [map_prod]
  have hIg : I.map φ = Ideal.span {g} := by rw [hI, hφg]

  let dd : Fin n → Derivation F R R := fun i => (bs.coord i).compDer (KaehlerDifferential.D F R)
  have hδ : ∀ i l, dd i (φ (x l)) = if l = i then 1 else 0 := by
    intro i l
    show bs.coord i (KaehlerDifferential.D F R (φ (x l))) = _
    rw [← hbs l, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let hm : Fin n → R := fun l => if l ∈ J.map e then φ (x l) else 1
  let E : Fin n → Derivation F R R := fun i => hm i • dd i
  have hEapp : ∀ i y, E i y = hm i * dd i y := fun i y => rfl

  have hEg : ∀ i, E i g ∈ Ideal.span {g} := by
    intro i
    rw [hEapp]
    by_cases hi : i ∈ J.map e
    · obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.mp hi
      have hsplit : g = r j0 * ∏ j ∈ J.erase j0, r j := (Finset.mul_prod_erase J r hj0).symm
      have hrest : dd (e j0) (∏ j ∈ J.erase j0, r j) = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ e j0 := fun h => (Finset.ne_of_mem_erase hj) (e.injective h)
        show dd (e j0) (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      have hone : dd (e j0) (r j0) = 1 := by
        show dd (e j0) (φ (x (e j0))) = 1
        rw [hδ, if_pos rfl]
      have hmv : hm (e j0) = r j0 := if_pos hi
      have : hm (e j0) * dd (e j0) g = g := by
        conv_lhs => rw [hsplit]
        rw [Derivation.leibniz, hrest, hone, hmv, smul_zero, zero_add, smul_eq_mul, mul_one, ← hsplit]
      rw [this]
      exact Ideal.mem_span_singleton_self g
    · have : dd i g = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ i := fun h => hi (Finset.mem_map.mpr ⟨j, hj, h⟩)
        show dd i (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      rw [this, mul_zero]
      exact Ideal.zero_mem _
  have hE : ∀ i, ∀ f ∈ I.map φ, E i f ∈ I.map φ := by
    intro i f hf
    rw [hIg] at hf ⊢
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hEg i))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
  choose N hN using fun i => GlobalTheory.T.logarithmicDerivation_localizationAtPrime_span_of_ring F A R P I n b hspan (E i) (hE i)

  choose D' hD' using fun k =>
    GlobalTheory.T.exists_derivation_extend_localization_atPrime ℤ A R P ((Algebra.linearMap A R).compDer (b k))
  have hD'a : ∀ k a, D' k (φ a) = φ (b k a) := fun k a => hD' k a
  have hD'I : ∀ k, ∀ f ∈ I.map φ, D' k f ∈ I.map φ := by
    intro k f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD'a]
      exact Ideal.mem_map_of_mem _ (hbI k a ha)
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy hy' =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy') (Ideal.mul_mem_right _ _ hy)
  have hdiv : ∀ l k, ∃ c, φ (b k (x l)) = hm l * c := by
    intro l k
    by_cases hl : l ∈ J.map e
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hl
      have hgk : D' k g ∈ Ideal.span {g} := by
        rw [← hIg]; exact hD'I k g (by rw [hIg]; exact Ideal.mem_span_singleton_self g)
      have := GlobalTheory.T.dvd_derivation_of_mem_span_prod_params' R m r hrsp J (D' k) hgk j hj
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      have hmv : hm (e j) = r j := if_pos hl
      rw [hmv, ← hc]
      exact (hD'a k (x (e j))).symm
    · refine ⟨φ (b k (x l)), ?_⟩
      have hmv : hm l = 1 := if_neg hl
      rw [hmv, one_mul]
  choose M hM using hdiv

  let Bm : Matrix (Fin n) (Fin n) R := Matrix.of fun l k => φ (b k (x l))
  have hBdet : φ (logDet b x) = Bm.det := by
    rw [logDet, RingHom.map_det]
    congr 1
  have h1 : Bm = Matrix.diagonal hm * Matrix.of M := by
    ext l k
    simp [Bm, Matrix.diagonal_mul, hM]
  have h2 : Matrix.diagonal hm = Bm * (Matrix.of N).transpose := by
    ext l i
    rw [Matrix.mul_apply]
    have hsum : ∑ k, Bm l k * (Matrix.of N).transpose k i = ∑ k, N i k * φ (b k (x l)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Bm, mul_comm]
    rw [hsum, ← hN i (x l), hEapp, hδ, Matrix.diagonal_apply]
    by_cases hli : l = i
    · subst hli; simp
    · simp [hli]
  have hdetD : (Matrix.diagonal hm).det = g := by
    rw [Matrix.det_diagonal]
    have : ∏ l, hm l = ∏ l ∈ J.map e, φ (x l) := by
      rw [← Finset.prod_filter]
      congr 1
      ext l; simp
    rw [this, Finset.prod_map]
  haveI : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hprime : ∀ j, Prime (r j) := ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hprime j).ne_zero
  have hMN : (Matrix.of M).det * (Matrix.of N).transpose.det = 1 := by
    have h3 : Matrix.diagonal hm = Matrix.diagonal hm * (Matrix.of M * (Matrix.of N).transpose) := by
      conv_lhs => rw [h2, h1]
      rw [Matrix.mul_assoc]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h4
    exact (mul_left_cancel₀ hg0 (h4.symm.trans (mul_one g).symm))
  refine ⟨Units.mkOfMulEqOne _ _ hMN, ?_⟩
  rw [Units.val_mkOfMulEqOne, hφg, hBdet, h1, Matrix.det_mul, hdetD, mul_comm]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.FormsLocus.exists_closed_formsOK) | (exact GlobalTheory.FormsLocus.exists_closed_formsOK) | (intros; apply GlobalTheory.FormsLocus.exists_closed_formsOK <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstChern_eq_sum_cup_invariantForms : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A L ψ → ∃ (I : Type) (_ : Fintype I) (c : I → primDR A) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (hω : ∀ k, Form.cl _ (ω k) ∈ primDR A), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (c k).1 (Form.cl _ (ω k))) ∧ ∀ f ∈ Fil A, ∀ x : HdR A, ψ f x = ∑ k, f (c k) * x ⟨_, hω k⟩ := by
  first | exact @GlobalTheory.PolForm.chern_eq_sum_cup_form | exact GlobalTheory.PolForm.chern_eq_sum_cup_form | (intros; apply GlobalTheory.PolForm.chern_eq_sum_cup_form <;> assumption)
end
