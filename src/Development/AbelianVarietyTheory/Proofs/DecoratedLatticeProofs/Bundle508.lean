module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle430
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle240
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle502
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto



theorem transferOn_inert : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun v => ¬ IsSplit (E := D.host.E) v := by
  intro hH D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hbne
  obtain ⟨hS, hT⟩ := hunr w h
  rcases hx with ⟨hs, -⟩ | ⟨hin, c, ϖ, eS, α, hUI, heS, hxS, rfl⟩
  · exact absurd hs hv
  obtain ⟨-, hodd, hch⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).2 hv
  obtain ⟨eT, heT⟩ := hch c heS.1
  have hf0 : (f : WO S T → ℂ) ≠ 0 := fun h0 => hbne (by rw [show f = 0 from Subtype.ext h0]; simp)
  obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, hcT, hcS⟩ :=
    GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hUI heS heT f hf hf0
  have hq0 : (qV D.host.F v : ℂ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  obtain ⟨hvS, hsegS⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS
  obtain ⟨hvT, -⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χT T.rank hW.hecT hW.resT v w h hin hT
  refine Or.inr ⟨hin, c, ϖ, eT, liftPar (Units.mk0 _ hq0) S.rank T.rank α, hUI, heT, ?_, ?_⟩
  · set α' := liftPar (Units.mk0 _ hq0) S.rank T.rank α
    have e1S : embV S v (eS.symm 1) = 1 := by rw [map_one, map_one]
    have e1T : embV T v (eT.symm 1) = 1 := by rw [map_one, map_one]
    have e0S : embV S v 1 = 1 := map_one _
    have e0T : embV T v 1 = 1 := map_one _
    obtain ⟨RS, hRS⟩ : ∃ RS : Representation ℂ (GU c S.rank) (WO S T → ℂ),
        ∀ g u, RS g u = om (embV S v (eS.symm g), 1) u :=
      ⟨om.comp ((MonoidHom.inl _ _).comp ((embV S v).comp eS.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨RT, hRT⟩ : ∃ RT : Representation ℂ (GU c T.rank) (WO S T → ℂ),
        ∀ g u, RT g u = om (1, embV T v (eT.symm g)) u :=
      ⟨om.comp ((MonoidHom.inr _ _).comp ((embV T v).comp eT.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨πS, hπS⟩ : ∃ πS : Representation ℂ (GU c S.rank) U, ∀ g (u : U), ((πS g u : U) : WO S T → ℂ) = RS g u :=
      ⟨GlobalTheory.PRep.sub RS U fun g u hu => by rw [hRS, ← e0T]; exact hU _ _ u hu, fun _ _ => rfl⟩
    obtain ⟨πT, hπT⟩ : ∃ πT : Representation ℂ (GU c T.rank) U, ∀ g (u : U), ((πT g u : U) : WO S T → ℂ) = RT g u :=
      ⟨GlobalTheory.PRep.sub RT U fun g u hu => by rw [hRT, ← e0S]; exact hU _ _ u hu, fun _ _ => rfl⟩
    have hMS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = RS g m := fun g m => by
      rw [hRS, hωom, e1T]
    have hMT : ∀ g (m : M), ((ω (1, g) m : M) : WO S T → ℂ) = RT g m := fun g m => by
      rw [hRT, hωom, e1S]
    have hvac := hstd.2.2.1
    have hfixS : ∀ k ∈ KU c S.rank, πS k f = f := fun k hk => by
      have a4 := hstd.1.fix k 1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 (one_mem _) s hvac
      apply Subtype.ext
      rw [hπS, ← hsf, ← hMS]; exact congrArg Subtype.val a4
    have hfixT : ∀ k ∈ KU c T.rank, πT k f = f := fun k hk => by
      have a4 := hstd.1.fix 1 k (one_mem _) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 s hvac
      apply Subtype.ext
      rw [hπT, ← hsf, ← hMT]; exact congrArg Subtype.val a4
    have hcom1 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI S.rank
    have hcom2 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI T.rank
    have hρ1 : ρ 1 x = x := by rw [map_one]; rfl
    have hbT : ∀ g (u : U), b (πT g u) x = ρ' (eT.symm g) (b u x) := fun g u => by
      have e2 := hb 1 (eT.symm g) u x
      have e : πT g u = ⟨om (embV S v 1, embV T v (eT.symm g)) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπT g u).trans ((hRT g u).trans (congrArg (fun z => om (z, embV T v (eT.symm g)) (u : WO S T → ℂ)) e0S.symm)))
      rw [hρ1] at e2
      rw [e, e2]
    have hbS : ∀ g (u : U) y, b (πS g u) (ρ (eS.symm g) y) = b u y := fun g u y => by
      have e2 := hb (eS.symm g) 1 u y
      have e : πS g u = ⟨om (embV S v (eS.symm g), embV T v 1) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπS g u).trans ((hRS g u).trans (congrArg (fun z => om (embV S v (eS.symm g), z) (u : WO S T → ℂ)) e0T.symm)))
      rw [map_one ρ', Module.End.one_apply] at e2
      rw [e, e2]
    refine ⟨hbne, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h' hh' => ?_⟩
    · show ρ' (eT.symm k) (b f x) = b f x
      rw [← hbT, hfixT k hk]
    · have : CharZero (w.adicCompletion D.host.E) :=
        charZero_of_injective_algebraMap (algebraMap D.host.E (w.adicCompletion D.host.E)).injective
      obtain ⟨h0, hh0, heq⟩ := GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller hH _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd h' hh'
      have hsat := GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd hcT hcS (by omega) h0 hh0 h' hh' heq
        (Units.mk0 _ hq0) rfl α
      have sA : b (heckeVec πT (KU c T.rank) h' f) x =
          heckeVec (ρ'.comp eT.symm.toMonoidHom) (KU c T.rank) h' (b f x) :=
        map_heckeVec hcom2.1 hh' (b.flip x) (fun g u => hbT g u) f
      have sB : heckeVec πT (KU c T.rank) h' f = heckeVec πS (KU c S.rank) h0 f := by
        apply Subtype.ext
        have m1 := map_heckeVec hcom2.1 hh' U.subtype (ρ' := RT) (fun g u => hπT g u) f
        have m2 := map_heckeVec hcom2.1 hh' M.subtype (ρ := ω.comp (MonoidHom.inr _ _)) (ρ' := RT) (fun g m => hMT g m) s
        have m3 := map_heckeVec hcom1.1 hh0 M.subtype (ρ := ω.comp (MonoidHom.inl _ _)) (ρ' := RS) (fun g m => hMS g m) s
        have m4 := map_heckeVec hcom1.1 hh0 U.subtype (ρ' := RS) (fun g u => hπS g u) f
        simp only [Submodule.subtype_apply] at m1 m2 m3 m4
        rw [m1, m4, ← hsf, ← m2, ← m3, heq]
      have sC := (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear (GU c S.rank) (KU c S.rank) hcom1.1 hcom1.2.1 U X X' πS (ρ.comp eS.symm.toMonoidHom) b
        (fun g u y => hbS g u y) f (GlobalTheory.LGrp.mem_fixed.2 hfixS) x hxS.2.1 h0 hh0).2
      have hev : (fun g => h0 g⁻¹) = h0 := funext fun g => hcom1.2.2 h0 hh0 g
      rw [← sA, sB, sC, hev, hxS.2.2 h0 hh0, map_smul, hsat]
  · have hc := GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment (Units.mk0 _ hq0) S.rank T.rank (by omega) α
    have ht' : ((T.rank : ℤ) - S.rank) = (t : ℤ) := by omega
    rw [ht'] at hc
    have e := congrArg (Multiset.map (((-1 : ℂˣ) ^ S.rank) * ·)) hc
    simp only [Multiset.map_map, Multiset.map_add (f := _), Function.comp_def, mul_inv_cancel_left] at e
    rw [Multiset.map_id'] at e
    rw [e, stepPar, hvS, hvT, hsegS (Units.mk0 _ hq0) _ t rfl]
    congr 1
    · exact Multiset.map_congr rfl fun y _ => by group

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaReduce

theorem conj_level {G ι : Type*} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (J : List ι) (f : ι → G) (x κ' : G) (κ : U)
    (hκ : κ.1 = (J.map f).prod * κ') (hc : x * κ' = κ' * x)
    (h1 : ∀ i, ∃ h : f i ∈ U, χ ⟨_, h⟩ = 1) (h2 : ∀ i, ∃ h : x⁻¹ * f i * x ∈ U, χ ⟨_, h⟩ = 1) :
    ∃ κ'' : U, κ.1 * x = x * κ''.1 ∧ χ κ'' = χ κ := by
  let K : Subgroup G := χ.ker.map U.subtype
  have hK : ∀ g, (∃ h : g ∈ U, χ ⟨_, h⟩ = 1) → g ∈ K := fun g ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩
  have hP : (J.map f).prod ∈ K := K.list_prod_mem fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact hK _ (h1 i)
  have hP' : (J.map f).prod ∈ K.comap (MulAut.conj x⁻¹).toMonoidHom := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    have := hK _ (h2 i)
    simpa using this
  have hP'' : x⁻¹ * (J.map f).prod * x ∈ K := by simpa using hP'
  obtain ⟨m, hm, hm'⟩ := K.mul_mem hP'' (K.inv_mem hP)
  have hm1 : χ m = 1 := hm
  have hm2 : m.1 = x⁻¹ * (J.map f).prod * x * (J.map f).prod⁻¹ := hm'
  refine ⟨m * κ, ?_, by rw [map_mul, hm1, one_mul]⟩
  rw [Subgroup.coe_mul, hm2, hκ, mul_assoc, ← hc]
  group

variable {D : D7}

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, GlobalTheory.FinPl.LocProd.mem_congGrp_entries]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, Matrix.sub_apply, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_anti (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P' w → P w) : grpOff V P ≤ grpOff V P' := by
  apply GlobalTheory.FinPl.LocProd.congGrp_mono
  intro a ha
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha ⊢
  exact fun w hw => ha w (h w hw)

end GlobalTheory.AdForm.DiaReduce


open GlobalTheory.AdForm.DiaReduce in
theorem GlobalTheory.AdForm.DiaReduce.rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (i : ℕ) (hi : i ≤ B.R.m) (φ) (hφ : φ ∈ (I.fm l u a).Fi i) (β : Ch i)
    (y : (I.chain l u a).Y i) (k : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (hk : k ∈ GinfC ((I.rec7 l Z).sp.X i)) :
    ∃ y' : (I.chain l u a).Y i, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ g, ∀ κ : A.U i β,
      A.rd θ i hi β φ y (γ * (g * k * κ.1)) = (A.chi i β κ : ℂ) * A.rd θ i hi β φ y' g := by
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
    (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
    (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
  obtain ⟨hL, hK, hR, -⟩ := laws
  let z := GlobalTheory.AdForm.Model.trFr θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) k (eY y)
  refine ⟨eY.symm z, fun γ hγ g κ => ?_⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U i hi β κ.1).1 κ.2
  have hchi := hA.chi i hi β κ κ' hκ'
  have e1 := hL γ hγ (g * k * κ.1)
  have e2 := hK κ.1 hκf κ' hκ' (g * k)
  have e3 := hR k hk z (fun τ => rfl) g
  exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e3))


open GlobalTheory.AdForm.DiaReduce in
theorem GlobalTheory.AdForm.diaSum_eq_zero_of_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y, (∀ (c : {c // A.chOf j c = b}) y', ∑ᶠ s, A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) = 0) → ∀ x, ∑ᶠ s, A.rd θ j hj b φ y (x * (β j i).gl (g s)) = 0 := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v _ g hg b y h0 x
  have hinj := GlobalTheory.AdForm.StdT.places_injective I hok hpins l Z u p β Q L hS
  obtain ⟨e, -⟩ := hS.1
  haveI : Finite ι := Finite.of_equiv _ e.symm
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hst, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA k ι p β Q L hS (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj b
  obtain ⟨γ, hγ, c, r, hr, κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hok hpins l Z u a Ch A hA j hj b).1.dec x
  obtain ⟨g', hg', κ', hκ', hκe⟩ := hdec κ hκ
  obtain ⟨y', hy'⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y r hr
  have hAt : ∀ i' t, (β j i').gl t ∈ grpAt ((I.rec7 l Z).sp.X j) (· = (p i').v) := fun i' t =>
    GlobalTheory.FinPl.FrameLat.gl_mem_grpAt (β j i') t
  have hcomm := ((GlobalTheory.FinPl.localComponents (I.rec7 l Z) (· = (p i).v)).2 ((I.rec7 l Z).sp.X j)).2.1
  have key : ∀ s, A.rd θ j hj b φ y (γ * (A.h j b c * r) * κ * (β j i).gl (g s)) =
      (A.chi j b ⟨κ, hκ⟩ : ℂ) * A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) := by
    intro s
    obtain ⟨κ'', h1, h2⟩ := conj_level (A.U j b) (A.chi j b) Finset.univ.toList (fun i' => (β j i').gl (g' i'))
      ((β j i).gl (g s)) κ' ⟨κ, hκ⟩ hκe
      (hcomm _ (hAt i _) _ (grpOff_anti _ (fun w hw => ⟨i, hw⟩) hκ')) (fun i' => hst i' _ (hg' i')) (fun i' => by
        by_cases hi : i' = i
        · subst hi
          rw [← map_inv, ← map_mul, ← map_mul]
          refine hst i' _ ?_
          rw [mul_smul, mul_smul, hg, smul_comm (g' i') s, hg', ← hg, inv_smul_smul]
        · have hc := hcomm _ (hAt i (g s)) _ (GlobalTheory.FinPl.LocProd.grpAt_le_grpOff' _ _ _
            (fun w hw hw' => hi (hinj (hw.symm.trans hw'))) (hAt i' (g' i')))
          rw [mul_assoc, ← hc, inv_mul_cancel_left]
          exact hst i' _ (hg' i'))
    have hc := hcomm _ (hAt i (g s)) r (real_le_off _ _ hr)
    have h1' : κ * (β j i).gl (g s) = (β j i).gl (g s) * κ''.1 := h1
    have e1 : γ * (A.h j b c * r) * κ * (β j i).gl (g s) = γ * (A.h j b c * (β j i).gl (g s) * r * κ''.1) := by
      rw [mul_assoc, h1', mul_assoc (A.h j b c), hc]
      simp only [mul_assoc]
    rw [e1, hy' γ hγ, h2]
  simp only [key]
  rw [← mul_finsum' _ _ (Set.toFinite _), h0, mul_zero]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.TransLaw

theorem trc_apply' {D : D7} {V : HSp D} (c : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc c f x = ∑ g ∈ c.support, c g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem list_prod_right {G : Type} [Group G] (F : G → ℂ) (L : List G) (hL : ∀ a ∈ L, ∀ z, F (z * a) = F z) (z : G) :
    F (z * L.prod) = F z := by
  induction L generalizing z with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, ← mul_assoc, ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (z * a), hL a List.mem_cons_self]

theorem list_prod_chi {G : Type} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (L : List G)
    (hL : ∀ a ∈ L, ∃ h : a ∈ U, χ ⟨a, h⟩ = 1) : ∃ h : L.prod ∈ U, χ ⟨_, h⟩ = 1 := by
  induction L with
  | nil => exact ⟨U.one_mem, χ.map_one⟩
  | cons a L ih =>
    obtain ⟨ha, hχa⟩ := hL a List.mem_cons_self
    obtain ⟨hP, hχP⟩ := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    refine ⟨by rw [List.prod_cons]; exact U.mul_mem ha hP, ?_⟩
    have e : (⟨(a :: L).prod, by rw [List.prod_cons]; exact U.mul_mem ha hP⟩ : U) = ⟨a, ha⟩ * ⟨L.prod, hP⟩ := by
      apply Subtype.ext; simp [List.prod_cons]
    rw [e, map_mul, hχa, hχP, one_mul]


theorem rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is) (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ)
    (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j) (b : Ch j) (y : (I.chain l u a).Y j) :
    (∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ g, A.rd θ j hj b φ y (γ * g) = A.rd θ j hj b φ y g) ∧
    (∀ κ : A.U j b, ∀ g, A.rd θ j hj b φ y (g * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y g) ∧
    (∀ k ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ y' : (I.chain l u a).Y j,
      IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
      ∀ g, A.rd θ j hj b φ y (g * k) = A.rd θ j hj b φ y' g) := by
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY
    ⟨A.kb j, hA.reads j hj⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨hL, hK, hR, -⟩ := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj b).lev {c // A.chOf j c = b}
      (A.K j hj b).y (A.K j hj b).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF b) ⟨y.1, y.2⟩
  refine ⟨fun γ hγ g => hL γ hγ g, fun κ g => ?_, fun k hk y' hy g => hR k hk ⟨y'.1, y'.2⟩ hy g⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U j hj b κ.1).1 κ.2
  rw [hA.chi j hj b κ κ' hκ']
  exact hK κ.1 hκf κ' hκ' g

end GlobalTheory.AdForm.TransLaw


open GlobalTheory.AdForm.TransLaw in

theorem GlobalTheory.AdForm.trc_rd_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ K _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv b y γ hγ e g0 hg0 κ y' hy
  obtain ⟨hLy, hKy, hRy⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y
  have hT' := hT
  obtain ⟨⟨eι, -⟩, -⟩ := hT'
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  obtain ⟨hstab, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA K ι p β Q L hT Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.2 (Finset.mem_univ _)) j hj b
  obtain ⟨gs, hgs, κ', hκ'off, hκeq⟩ := hdec κ.1 κ.2
  set s := (Finset.univ.toList.map fun i => (β j i).gl (gs i)).prod with hs
  obtain ⟨hsU, hχs⟩ := list_prod_chi (A.U j b) (A.chi j b) (Finset.univ.toList.map fun i => (β j i).gl (gs i)) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab i (gs i) (hgs i))
  have hκ'U : κ' ∈ A.U j b := by
    have : κ' = s⁻¹ * κ.1 := by rw [hκeq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact (A.U j b).mul_mem ((A.U j b).inv_mem hsU) κ.2
  have hχκ : A.chi j b κ = A.chi j b ⟨κ', hκ'U⟩ := by
    have e1 : κ = (⟨s, hsU⟩ : A.U j b) * ⟨κ', hκ'U⟩ := Subtype.ext hκeq
    rw [e1, map_mul, hχs, one_mul]
  set F := trc c (A.rd θ j hj b φ y) with hF

  have hcomm : ∀ g' ∈ c.support, κ' * g' = g' * κ' := fun g' hg' =>
    ((GlobalTheory.FinPlLoc.part_grp (fun x => ∃ i, x = (p i).v) ((I.rec7 l Z).sp.X j)).2.1 g' (hc g' hg') κ' hκ'off).symm

  have step1 : ∀ x, F (x * κ.1) = (A.chi j b κ : ℂ) * F (x * s) := by
    intro x
    rw [hF, trc_apply', trc_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' hg' => ?_
    rw [hκeq, ← mul_assoc, mul_assoc (x * s), hcomm g' hg', ← mul_assoc, hKy ⟨κ', hκ'U⟩, hχκ]
    ring

  have step2 : ∀ x, F (x * s) = F x := by
    intro x
    refine list_prod_right F _ ?_ x
    intro a' ha' z
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha'
    exact congrFun (hinv b y i (gs i) (hgs i)) z

  have step3 : F (γ * (A.h j b e * g0)) = trc c (A.rd θ j hj b φ y') (A.h j b e) := by
    rw [hF, trc_apply', trc_apply']
    refine Finset.sum_congr rfl fun g' hg' => ?_
    have hfin : g' ∈ GfC ((I.rec7 l Z).sp.X j) := GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hc g' hg')
    rw [mul_assoc γ, hLy γ hγ, mul_assoc, ← GlobalTheory.FinTranslate.comm_fin_real _ hfin hg0, ← mul_assoc,
      hRy g0 hg0 y' hy]
  rw [step1, step2, step3]
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylStd.main | exact GlobalTheory.StdUnn.WeylStd.main | (intros; apply GlobalTheory.StdUnn.WeylStd.main <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, ∃ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS := by
  first | exact @GlobalTheory.StdUnn.exists_transport_std | exact GlobalTheory.StdUnn.exists_transport_std | (intros; apply GlobalTheory.StdUnn.exists_transport_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlaces_group_eq_product_local_groups : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QProd.prod_local | exact GlobalTheory.QProd.prod_local | (intros; apply GlobalTheory.QProd.prod_local <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QSuppTwo.main | exact GlobalTheory.QSuppTwo.main | (intros; apply GlobalTheory.QSuppTwo.main <;> assumption)
end
