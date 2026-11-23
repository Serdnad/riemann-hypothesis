module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle409
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
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
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas

@[expose] public section

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn.UnipLevel

theorem pow_apply_eq_zero_of_strict {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin n) (Fin n) K)
    (hS : ∀ a b : Fin n, b ≤ a → S a b = 0) (m : ℕ) :
    ∀ a b : Fin n, (b : ℕ) < a + m → (S ^ m) a b = 0 := by
  induction m with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply, if_neg]
    intro hab
    rw [hab] at h
    omega
  | succ m ih =>
    intro a b h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : b ≤ j
    · rw [hS j b hj, mul_zero]
    · have hj' : (j : ℕ) < a + m := by
        have : (j : ℕ) < b := Fin.lt_def.1 (not_le.1 hj)
        omega
      rw [ih a j hj', zero_mul]

end GlobalTheory.ShareOn.UnipLevel
namespace GlobalTheory.ShareOn.UnipLevel




theorem levUnip_mod_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r hr i u k v hU x
  classical
  obtain ⟨v'⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev : Formalism.IndefR.FWT.LevIs (R2 p) i (Formalism.IndefR.FWT.iotaW p.T i) p.T.Q.l.M (Mfr p.T.Q.l)
      (fun g => liftLa (r.lev i g)) := hr.level v' i
  have hL := hr.laws v'
  have hι : LatEmb (Wc D i) (Formalism.IndefR.FWT.iotaW p.T i) := GlobalTheory.TraceLattice.latEmb_iotaW hL i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨plg, iso, hplg, -, -, hG⟩ := p.grpRecPin
  have hrk : D.R.r = (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q :=
    (hL.j.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ (r.used v').full.toCore.good_σ₀).1
  set PPs := plg ⟨k, v⟩ with hPPs
  obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) hβ _ _ hι PPs.1
  obtain ⟨κ, hκ, hκa⟩ := hlev u
  have hMbP : p.T.Q.l.Mb ≤ PPs.1.asIdeal := by
    rw [hr.half]
    exact Ideal.prod_le_inf.trans (Finset.inf_le PPs.2)
  have hM : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PPs.1.asIdeal := hMbP (GlobalTheory.LevDesc.natCast_M_mem _)
  have hSt : Lev.finE (Wc D i) κ ∈ St ((R2 p).βW i) := parLev_St hκ.2.1
  have hkill : ∀ c ∈ PPs.1.asIdeal, ∀ y, φ (c • y) = 0 := by
    intro c hc y
    rw [map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_mul]
  have hcop : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  obtain ⟨c₁, hc₁, w, hw, hcw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
  set f := liftLa (r.lev i u) with hf
  set N : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP PPs.1) :=
    (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)).1 with hN
  have hfφ : ∀ a, φ (f a) = N *ᵥ φ a := by
    intro a
    have ha : a = c₁ • a + w • a := by rw [← add_smul, hcw, one_smul]
    have h1 := hφk κ hSt p.T.Q.l.M hM (w • a) (f (w • a)) (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
    have h2 : φ (w • a) = φ a := by
      conv_rhs => rw [ha]
      rw [map_add (f := _), hkill c₁ (hMbP hc₁), zero_add]
    have h3 : φ (f a) = φ (f (w • a)) := by
      conv_lhs => rw [ha]
      rw [map_add (f := _), map_add (f := _), map_smul, hkill c₁ (hMbP hc₁), zero_add]
    rw [h3, h1, h2]
  have hrank : (Wc D i).rank = D.R.r := Formalism.IndefR.FWT.rank_Wc i
  have h5 : (R2 p).eG u PPs = upperLeftBlock ((R2 p).datWp i (R2 p).triv).hr (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)) :=
    (congrFun hκ.2.2 PPs).symm
  have h6 := upper_block_val_submatrix ((R2 p).datWp i (R2 p).triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 PPs.2))
  have h7 : (R2 p).eG u PPs = Formalism.UG.bc (iso ⟨k, v⟩ : ZMod (D.host.g k) →+* kP PPs.1) ((p.R.eG.trans p.cG) u ⟨k, v⟩) :=
    hG u ⟨k, v⟩
  rw [← h5, h7] at h6
  have hsub : ∀ a' b' : Fin D.R.r, N (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr a') (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr b') =
      iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) a' b') := by
    intro a' b'
    have := congrFun (congrFun h6 a') b'
    exact this.symm
  have hstrict : ∀ a b : Fin (Wc D i).rank, b ≤ a → (N - 1) a b = 0 := by
    intro a b hab
    have ha' : (a : ℕ) < D.R.r := hrank ▸ a.2
    have hb' : (b : ℕ) < D.R.r := hrank ▸ b.2
    have e1 : N a b = iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))
        ⟨a, ha'⟩ ⟨b, hb'⟩) := hsub ⟨a, ha'⟩ ⟨b, hb'⟩
    rw [Matrix.sub_apply, e1]
    rcases lt_or_eq_of_le hab with h | h
    · rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).1 h, map_zero, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · have hab' : (⟨a, ha'⟩ : Fin D.R.r) = ⟨b, hb'⟩ := by
        ext; show (a : ℕ) = b; rw [h]
      rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).2 hab', map_one, h, Matrix.one_apply_eq, sub_self]
  have hnil : (N - 1) ^ D.R.r = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    exact pow_apply_eq_zero_of_strict _ hstrict D.R.r a b (by have := b.2; omega)
  have hpow : ∀ (m : ℕ) a, φ (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) = ((N - 1) ^ m) *ᵥ φ a := by
    intro m
    induction m with
    | zero => intro a; rw [pow_zero, pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hfφ, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hker : ∀ y, φ y = 0 → y ∈ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
    intro y hy
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI hfin : Finite (kP PPs.1) := Finite.of_equiv _ (iso ⟨k, v⟩).toEquiv
    haveI : Finite (𝓞 D.host.E ⧸ PPs.1.asIdeal) := hfin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).fin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).proj
    have hle : PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ≤ LinearMap.ker φ := by
      rw [Submodule.smul_le]
      intro c hc z _
      exact hkill c hc z
    let ψ := (PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).liftQ φ hle
    have hψs : Function.Surjective ψ := by
      intro z
      obtain ⟨y', rfl⟩ := hφs z
      exact ⟨Submodule.Quotient.mk y', rfl⟩
    have hc0 : Nat.card (kP PPs.1) ≠ 0 := Nat.card_pos.ne'
    have hN1 : Nat.card ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) =
        Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [GlobalTheory.natCard_quot_smul_top_of_projective, (p.T.Q.Dw ((i : ℕ) + 1)).rank, ← hrk, hrank]
    have hN2 : Nat.card (Fin (Wc D i).rank → kP PPs.1) = Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    haveI : Finite ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) :=
      Nat.finite_of_card_ne_zero (by rw [hN1]; exact pow_ne_zero _ hc0)
    have hb := hψs.bijective_of_nat_card_le (by rw [hN1, hN2])
    have h0 : ψ (Submodule.Quotient.mk y) = ψ 0 := by
      rw [map_zero]
      exact hy
    exact (Submodule.Quotient.mk_eq_zero _).1 (hb.1 h0)
  have hmk : ∀ (m : ℕ) a, ((((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ m)
      ((p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ a)) =
      (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ
        (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hf, ← liftLa_spec,
        ← map_sub, ← hf, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ((plg ⟨k, v⟩ : ↥p.R.Pg) : Pl D.host.E) = D.naut.plGw k v := hplg ⟨k, v⟩
  rw [← hP, ← hPPs]
  have hx := hmk D.R.r a
  rw [Submodule.mkQ_apply] at hx
  rw [hx]
  refine GlobalTheory.LevDesc.map_mem_smul_top _ (hker _ ?_)
  rw [hpow, hnil, Matrix.zero_mulVec]

end GlobalTheory.ShareOn.UnipLevel

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_measY (t : T) (j : ℕ) : ∃ (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
    (j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) ∧
    (j = D.R.m - 1 → IsMeasDef (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) μ 𝓕) := by
  have hLev := GlobalTheory.Mem.LevelOK.levOK_all D
  by_cases hj : j = D.R.m - 1
  · subst hj
    obtain ⟨μ, 𝓕, hμ⟩ := measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D)
      (Yc D (D.R.m - 1)) _ (D.sp.Y_sig _) (GlobalTheory.Mem.EasyInputs.spOK D).1
      (hLev _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)).1
    exact ⟨μ, 𝓕, fun h2 => absurd h2 (by omega), fun _ => hμ⟩
  · obtain ⟨μ, 𝓕, hμ⟩ := Formalism.IndefR.Eqv.measFDExists_holds D (Yc D j) (D.sp.Y_sig _) _ (hLev _ (R.βY j) (R.datYt t j R.triv)).1
    exact ⟨μ, 𝓕, fun _ => hμ, fun h' => absurd h' hj⟩

theorem exists_measX (t : T) : ∃ μ 𝓕, IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) D.sp.X' _ D.sp.X'_sig
    (GlobalTheory.Mem.EasyInputs.spOK D).2 (GlobalTheory.Mem.LevelOK.levOK_all D _ R.βX (R.datXt t)).1

theorem exists_measV (hv : ∀ i, (Vc D i).IsPosDef) (i : Fin D.R.m) (t : T) :
    ∃ μ 𝓕, IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) μ 𝓕 :=
  measDef_exists (Formalism.IndefR.Eqv.measLevDefExists_holds D) (Formalism.IndefR.Eqv.fundDomExists_holds D) (Vc D i) _ (D.sp.V_sig _)
    (fun τ => Or.inl (hv i τ)) (GlobalTheory.Mem.LevelOK.levOK_all D _ (R.βV i) (R.datVt i t)).1



theorem exists_modX (t : T) : ∃ (H : HMod (Bridge.Gf D.sp.X' → R.cX.W)) (j : A.fam.amb.FR t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J (levEnv _ R.βX (R.datXt t)).χ)
      (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) ∧ ∀ x, H.e (j x) = R.B.jR t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ) (Bridge.adInner (Bridge.ratF D.sp.X') (levEnv _ R.βX (R.datXt t)).J (R.B.R t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := R.cX.W) (R.B.R t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.R t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jR t) (fun x => by exact (R.B.R t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)



theorem exists_modV (i : Fin D.R.m) (t : T) :
    ∃ (H : HMod (Bridge.Gf (Vc D i) → (R.cV i).W)) (j : A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] H.H),
    H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
        (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) ∧
    ∀ x, H.e (j x) = R.B.jL i t x := by
  have herm : Formalism.IndefR.PeterssonHilbertSpace.IsHermPos (Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ)
      (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y) :=
    hermPos_of_ipOn (Bridge.adInner_ipOn (W := (R.cV i).W) (R.B.L i t).pres.reps (fun c => by
      exact ne_of_eq_of_ne ((R.B.L i t).pres.card_stab c) (Nat.pos_iff_ne_zero.mp (by apply Formalism.L2.DIV.CSD.wt_pos))))
  refine (hMod_of_herm herm).elim fun H hH => ?_
  have x := hMod_lift hH (R.B.jL i t) (fun x => by exact (R.B.L i t).pres.extMem_holds x)
  refine x.elim fun j hj => ⟨H, j, hH, ?_⟩
  exact (hj)

variable {R}

open Classical in
theorem idem_of_is {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (t : T) :
    Disjoint L.Pg (L.Q t) ∧ ∃ e : AE D, IsIdemSum e (L.Pg ∪ L.Q t) :=
  ⟨(GlobalTheory.ChainEquiv.places_sep L μ0 hL t).2, GlobalTheory.CentralShift.exists_idemSum _ fun _ hP _ hP' =>
    GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')⟩

theorem sd_of_frame {V : HSp D} {β Λ N} (h : IsSDFrame V β Λ N) : IsSelfDualC V Λ ∧ IsFrame β Λ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc, hc.1⟩

theorem exists_kerY (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T) (k : ℕ)
    (hv : k + 1 < D.R.m → IsVacO R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1)) (R.vac k)) :
    ∃ ω v, k + 1 < D.R.m → IsWeilDatumO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k) (R.ΛY (k + 1))
        (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) v := by
  by_cases hk : k + 1 < D.R.m
  · have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).1 k hk
    obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D k) (Yc D (k + 1)) _ _
      (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    have s1 := sd_of_frame (hL.βY k (by omega))
    have s2 := sd_of_frame (hL.βY (k + 1) hk)
    obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
      (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vac k) (hv hk)
    exact ⟨ω, v, fun _ => ⟨hω, hv'⟩⟩
  · exact ⟨1, 0, fun h => absurd h hk⟩

theorem exists_kerX (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (t : T)
    (hv : IsVacO R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX R.vacX) :
    ∃ ω v, IsWeilDatumO R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 ω ∧
      IsStepVecOf R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX) (R.ΛY (D.R.m - 1)) R.ΛX
        (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) R.vacX v := by
  have hm : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.1
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Yc D (D.R.m - 1)) D.sp.X' _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βY _ hm)
  have s2 := sd_of_frame hL.βX
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceDatum.stepVecExists D R.ψ R.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (R.MY (D.R.m - 1))) (cart R.MX)
    (R.ΛY (D.R.m - 1)) R.ΛX (R.βY (D.R.m - 1)) R.βX (R.datYt t (D.R.m - 1) R.triv) (R.chi D.R.m) (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2
    (idem_of_is hL t).1 (idem_of_is hL t).2 R.vacX hv
  exact ⟨ω, v, hω, hv'⟩

theorem exists_kerP (hL : R.toLevCh.Is A.μ0) (hψ : IsStdChar D R.ψ (-1)) (i : Fin D.R.m) (t : T)
    (hv : IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i)) :
    ∃ ω v, IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 ω ∧
      IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
        R.Pg (R.Q t) (R.xiR t) (R.vacP i) v := by
  have hs := (GlobalTheory.HeckeCharacterRestriction.splitFacts hL t).2.2 i
  obtain ⟨ω, hω⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D R.ψ hψ (Vc D i) (Wc D i) _ _
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have s1 := sd_of_frame (hL.βV i)
  have s2 := sd_of_frame (hL.βW i)
  obtain ⟨v, hv'⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i)
    (R.βV i) (R.βW i) R.Pg (R.Q t) (R.xiR t) s1.1 s2.1 s1.2 s2.2 (idem_of_is hL t).1 (idem_of_is hL t).2 (R.vacP i) hv
  exact ⟨ω, v, hω, hv'⟩

end GlobalTheory.TupExt

end
end

section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem qeRing_of_finiteType_int : ∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], FinalTheorems.QERing A := by
  intro A _ _
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  refine ⟨hN, fun P _ => ⟨?_, ?_⟩, fun B _ _ _ => ?_⟩
  · exact AdicCompletion.flat_of_isNoetherian _
  · apply GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
    intro K _ _ _
    haveI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
      Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime P) :=
      Algebra.EssFiniteType.comp ℤ A (Localization.AtPrime P)
    have hZ : @Algebra.EssFiniteType ℤ (Localization.AtPrime P) _ _ (Ring.toIntAlgebra _) := by
      convert this
      exact Subsingleton.elim _ _
    exact @GlobalTheory.T.formalFibre_isRegularRing_essFiniteType_int (Localization.AtPrime P) K _ _ hZ _ _ _
  · haveI : Algebra.FiniteType ℤ B := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ A) ‹_›
    haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
    exact GlobalTheory.T.isOpen_regularLocus_of_nagata' B (fun p _ => GlobalTheory.T.exists_regular_quotient_near_prime_finiteType_int B p)

end GlobalTheory
end
