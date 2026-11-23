module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
public import Formalism.LocalToGlobal.Columns.RecLevelSym
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle401
public import Formalism.LocalToGlobal.Columns.TwQLevU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle404
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
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.PsiTie

theorem symPos_eq_symm {r k rS : ℕ} (hr : k + rS ≤ r) (i : Fin r) :
    symPos r rS k i = (Formalism.L2.Col.symPerm r k rS).symm i := by
  apply Fin.ext
  rw [Formalism.L2.Col.symPerm_symm_val hr]
  unfold symPos Formalism.L2.Col.symIdxInv
  have hi := i.2
  show (if i.val < rS then k + i.val else if i.val < rS + k then i.val - rS else i.val) % r = _
  rw [Nat.mod_eq_of_lt (by split_ifs <;> omega)]
  split_ifs <;> omega

theorem symPos_entries_iff {κ : Type} [CommRing κ] {r k rS : ℕ} (hr : k + rS ≤ r) (M y : GL (Fin r) κ) :
    (∀ i j : Fin r, (M : Matrix (Fin r) (Fin r) κ) (symPos r rS k i) (symPos r rS k j) =
      (y : Matrix (Fin r) (Fin r) κ) i j) ↔ Formalism.L2.Col.toSymOrd κ r k rS M = y := by
  simp only [symPos_eq_symm hr]
  constructor
  · intro h
    exact Units.ext (Matrix.ext fun i j => by rw [Formalism.L2.Col.toSymOrd_val]; exact h i j)
  · rintro rfl i j
    rfl

theorem baseLevel_character_preserved_placewiseIdentity {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {S T : Finset (Pl E)}
    (hT : T = S) (e : G0 S r ≃* G0 T r) (he : ∀ g P (h : P ∈ S) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) :
    (∀ g, g ∈ (P0 S r ψ).H ↔ e g ∈ (P0 T r ψ).H) ∧
      ∀ (g : (P0 S r ψ).H) (h : e g ∈ (P0 T r ψ).H), (P0 S r ψ).chi g = (P0 T r ψ).chi ⟨e g, h⟩ := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  refine ⟨fun g => by rw [hid], fun g h => ?_⟩
  exact congrArg _ (Subtype.ext (hid g).symm)

theorem piChar_apply' {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    Formalism.L2.Col.piChar H lam x = ∏ i, lam i (Formalism.L2.Col.piProj H i x) :=
  by simp [Formalism.L2.Col.piChar]

theorem ofLocal_chi_apply {E : Type} [Field E] [NumberField E] {LL : Type} [CommRing LL] {r : ℕ} {Pg : Finset (Pl E)}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* LLˣ) (x : ↥(Subgroup.pi Set.univ Hl)) :
    (LevelP.ofLocal Hl cl).chi x = ∏ PP, cl PP (LevelP.prj Hl PP x) :=
  by
    change (∏ PP : ↥Pg, (cl PP).comp (LevelP.prj Hl PP)) x = _
    exact map_prod (MonoidHom.eval x) _ _

theorem sym_tie {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    {T : Finset (Pl X.E)} (hT : T = Pr.vGs) (e : Formalism.L2.Col.G0 X.E Pr.vGs R.r ≃* G0 T R.r)
    (he : ∀ g P (h : P ∈ Pr.vGs) (h' : P ∈ T), e g ⟨P, h'⟩ = g ⟨P, h⟩)
    (ψ : ∀ PP : Pl X.E, AddChar (kP PP) X.K) (hψ : ∀ P (h : P ∈ Pr.vGs), ψ P = Ch.psi0 ⟨P, h⟩) :
    (∀ g, g ∈ (Formalism.L2.Col.rPsymF Ch).grp ↔ ∃ y ∈ (PsharpSym T R.r R.rS R.k ψ).H, ∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        ((y PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) ∧
    ∀ (g : (Formalism.L2.Col.rPsymF Ch).grp) (y : (PsharpSym T R.r R.rS R.k ψ).H), (∀ (PP : ↥T) (i j : Fin R.r),
      ((e g PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) (symPos R.r R.rS R.k i) (symPos R.r R.rS R.k j) =
        (((y : G0 T R.r) PP : GL (Fin R.r) (kP PP.1)) : Matrix (Fin R.r) (Fin R.r) (kP PP.1)) i j) →
      (Formalism.L2.Col.rPsymF Ch).chr g = (PsharpSym T R.r R.rS R.k ψ).chi y := by
  subst hT
  have hid : ∀ g, e g = g := fun g => funext fun P => he g P.1 P.2 P.2
  have hr : R.k + R.rS ≤ R.r := by have := Formalism.L2.Col.r_eq_sym R; omega
  refine ⟨fun g => ?_, fun g y hgy => ?_⟩
  · rw [hid]
    constructor
    · intro hg
      refine ⟨fun PP => Formalism.L2.Col.toSymOrd _ R.r R.k R.rS (g PP), (Subgroup.mem_pi _).2 fun PP _ => ?_,
        fun PP => (symPos_entries_iff hr _ _).2 rfl⟩
      have := (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _)
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS at this
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap] at this
      exact this
    · rintro ⟨y, hy, hyg⟩
      refine (Subgroup.mem_pi _).2 fun PP _ => ?_
      change g PP ∈ Formalism.L2.Col.HPsymF _ R.r R.k R.rS
      rw [Formalism.L2.Col.HPsymF_eq_comap_unipSym, Subgroup.mem_comap, (symPos_entries_iff hr _ _).1 (hyg PP)]
      exact (Subgroup.mem_pi _).1 hy PP (Set.mem_univ _)
  · rw [hid] at hgy
    have h1 := piChar_apply' (fun w => (Formalism.L2.Col.rPsymF Ch w).H) (fun w => (Formalism.L2.Col.rPsymF Ch w).lam) g
    have h2 := ofLocal_chi_apply (fun PP : ↥Pr.vGs => unipSym (kP PP.1) R.r R.rS R.k)
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) R.r R.rS R.k)) y
    refine h1.trans (Eq.trans ?_ h2.symm)
    refine Finset.prod_congr rfl fun w _ => ?_
    have hy : (y : G0 Pr.vGs R.r) w = Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) :=
      ((symPos_entries_iff hr _ _).1 (hgy w)).symm
    have hM : Formalism.L2.Col.toSymOrd _ R.r R.k R.rS ((g : Formalism.L2.Col.G0 X.E Pr.vGs R.r) w) ∈ unipSym (kP w.1) R.r R.rS R.k := by
      rw [← hy]; exact (Subgroup.mem_pi _).1 y.2 w (Set.mem_univ _)
    apply Units.ext
    have e1 := Formalism.L2.Col.chiSym_eq_symHom (Ch.psi0 w) R.r R.k R.rS
      ⟨_, Formalism.L2.Col.mem_HPsymF.1 ((Subgroup.mem_pi _).1 g.2 w (Set.mem_univ _))⟩ hM
    refine e1.trans ?_
    rw [hψ w.1 w.2]
    congr 2
    exact Subtype.ext hy.symm

theorem psiPPTie_of_levOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  intro X px I U L eG cG plg iso hOk hLev hId hpl hbc
  have hψ : ∀ P (h : P ∈ (X.B.primes px).vGs), psiC I P = I.Ch.psi0 ⟨P, h⟩ := fun P h => psiC_of_mem I h
  have hP0 := baseLevel_character_preserved_placewiseIdentity (S := (X.B.primes px).vGs) hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I)
  have hS := sym_tie I.Ch hLev.Pg eG (fun g P h h' => hId g P h h') (psiC I) hψ
  refine ⟨L.Pg, plg, fun kv => (iso kv).symm, psiC I, eG, ?_, ?_⟩
  · refine ⟨hpl, ?_, ?_, hP0.1, hP0.2, hS.1, hS.2⟩
    · intro g kv
      rw [hbc g kv]
      apply Units.ext
      ext i j
      simp [Matrix.GeneralLinearGroup.map, Formalism.UG.bc]
    · intro PP hPP
      rw [hLev.Pg] at hPP
      rw [psiC_of_mem I hPP]
      exact hOk.ch_ok.psi_zero_nontrivial_character _
  · intro kv c b hb
    have hw : ((plg kv : L.Pg) : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs := hLev.Pg ▸ (plg kv).2
    have h := hOk.weil ⟨_, hw⟩ c b hb
    rw [psiC_of_mem I hw]
    refine h.trans ?_
    have hq : Formalism.L2.Col.qOf ((⟨_, hw⟩ : {w // w ∈ (X.B.primes px).vGs}) : Pl X.B.fields.E) = X.toD7.host.g kv.1 :=
      absNorm_eq_of_res X.toD7 (iso kv).symm
    rw [hq]

end GlobalTheory.Mem.PsiTie
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem famR_places : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ t P, P ∈ (famR X I hX U Xg tr).A.ok t ↔
      Bridge.SplitOff (P.1 : Pl X.toD7.host.E) ((L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)))) ∧
    (∀ PP, Bridge.SplitOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ P : PlS X.B px, (P.1 : Pl X.toD7.host.E) = PP) ∧
    Bridge.InertTie (famR X I hX U Xg tr) (fun Q : PlI X.B px => (Q.1 : Pl X.toD7.host.E)) (L.Pg : Set (Pl X.toD7.host.E)) L.Q ∧
    (∀ PP, Bridge.InertOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ Q : PlI X.B px, (Q.1 : Pl X.toD7.host.E) = PP) := by
  intro X px I hX U Xg tr L eG _ _ hL _
  have hS : ∀ t : TupU I U, ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) :
        Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)) := by
    intro t
    rw [hL.Pg, hL.Q t]
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
      show Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t) : Chr X.B.fields.F X.B.fields.E X.B.fields.K) = _
      rw [tup_ixOf I t]
    rw [e]
    simp [Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG]
    rfl
  have hS0 : ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      (((X.B.primes px).vGs : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) := by
    rw [hL.Pg]
    simp
    rfl
  refine ⟨fun t P => ?_, fun PP hPP => ?_, ⟨Subtype.val_injective, fun t Q => ?_⟩, fun PP hPP => ?_⟩
  · show P.1 ∈ Formalism.L2.DIV.offSet ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ ↔ _
    unfold Formalism.L2.DIV.offSet Formalism.IndefR.Bridge.SplitOff
    rw [Set.mem_setOf_eq, hS t]
    exact Iff.rfl
  · obtain ⟨h1, h2, h3⟩ := hPP
    refine ⟨⟨PP, h1, ?_, fun Q hQ => h3 Q ?_⟩, rfl⟩
    · rw [hS0]; exact h2
    · rw [← hS0]; exact hQ
  · show Q.1 ∉ _ ↔ _
    unfold Formalism.IndefR.Bridge.InertOff
    rw [hS t]
    have hc : ∀ P : Pl X.toD7.host.E, Formalism.L2.Col.conjPrime₂ P = P →
        Formalism.HermitianLatticesTheory.conjIdeal (K := X.toD7.host.E) P.asIdeal = P.asIdeal := fun P hP => by
      rw [Formalism.L2.Col.conjIdeal_asIdeal, hP]
    exact ⟨fun h => ⟨hc Q.1 Q.2.1, h⟩, fun h => h.2⟩
  · obtain ⟨h1, h2⟩ := hPP
    have hc : Formalism.L2.Col.conjPrime₂ PP = PP := HeightOneSpectrum.ext (by rw [← Formalism.L2.Col.conjIdeal_asIdeal]; exact h1)
    have hin : ∃ x : 𝓞 X.toD7.host.E, Formalism.L2.Col.cO X.toD7.host.E x - x ∉ PP.asIdeal := by
      obtain ⟨θ, t, ht, hθ⟩ := X.toD7.sp.cm.cmUnram.2.2 PP.asIdeal PP.isMaximal
      have e : Formalism.L2.Col.cO X.toD7.host.E θ = t := RingOfIntegers.ext ht.symm
      refine ⟨θ, fun h => hθ ?_⟩
      rw [e] at h
      rw [← neg_sub]
      exact PP.asIdeal.neg_mem h
    refine ⟨⟨PP, hc, hin, ?_⟩, rfl⟩
    rw [hS0]; exact h2

end GlobalTheory.Mem.R3

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_memberStep_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m), ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u I.mu0 i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), I.ReadsK l Z u I.mu0 i hi chOf K ∧ (∀ c, ((K (chOf c)).y ⟨c, rfl⟩).1 = I.yStd u i c) ∧ ((i = 0 ∨ i = B.R.m) → Nonempty (Unique Ch)) := by
  first | exact @GlobalTheory.Mem.Col2.MemChart.exists_charts | exact GlobalTheory.Mem.Col2.MemChart.exists_charts | (intros; apply GlobalTheory.Mem.Col2.MemChart.exists_charts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.dualLattice_localBasis_iff_unimodularCompanion : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (u : B.Word) (a : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u a w → ∀ (i : ℕ) (hi : i ≤ B.R.m) (c : (I.stp u a i).Cl) (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c))) Bm ↔ Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u a i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm := by
  first | exact @GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | exact GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N | (intros; apply GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev


theorem _root_.GlobalTheory.T.congruenceOne_matrices_mem_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ N ∈ nhds (1 : GL (Fin n) (AfE F E)), ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → 0 < m →
      ∀ k : GL (Fin n) (AfE F E), GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k → GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) k⁻¹ → k ∈ N := by
  first | exact @GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | exact GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds | (intros; apply GlobalTheory.Mem.ColAd.Nbhd.congOne_nhds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem frExact_of_isPtOf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Θ q hQ g p hp
  have h1 : IsPtOf hc (g * 1) p := by rwa [mul_one]
  have hres : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 (((1 : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (((1 : DiaG (E := E) (ST := ST)) P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) else 0) := by
    intro P r j _
    rw [inv_one, Units.val_one]
    by_cases h : j = r
    · subst h
      rw [Matrix.one_apply_eq, map_one, if_pos rfl]
      simpa using hasRes_coe P.1 1
    · rw [Matrix.one_apply_ne (Ne.symm h), map_zero, if_neg h]
      simpa using hasRes_coe P.1 0
  obtain ⟨hU, hd⟩ := GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul F E hc n ST SG Q g 1 p 1 h1 ⟨DecoF.base E n ∅ ∅ ∅, isPtOf_base hc, rfl⟩
    (fun w _ => map_one _) hres
  rw [DecoSet.dia_one] at hd
  refine ⟨hU, hd, fun P => Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [qdf_at_val]
  show qPi q P ((g : Matrix (Fin n) (Fin n) _) i j) = q.phi P (((qGL n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [qsp_toGLm_apply]
  exact GlobalTheory.T.splitLocalLevel_firstFactor_reads_component hc n q P (hQ P) _ _ (hp.fr P i j)

end GlobalTheory.Mem.Col2.ChEx
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibleBasePoint_unitary_normalisesLevel : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG (E := E) (ST := ST)), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.basePt_facts | exact GlobalTheory.Mem.Col2.ChEx.basePt_facts | (intros; apply GlobalTheory.Mem.Col2.ChEx.basePt_facts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  first | exact @GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | exact GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | (intros; apply GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.heckeMultiplicity_eq_finrank_jointEigenspace : ∀ (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ) (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i), X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w)) (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := by
  first | exact @GlobalTheory.HeightCounting.mult_eq_finrank_jointEig | exact GlobalTheory.HeightCounting.mult_eq_finrank_jointEig | (intros; apply GlobalTheory.HeightCounting.mult_eq_finrank_jointEig <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SplitOutPlace



theorem not_mem_gPl_qPl : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := by
  intro D cf C tp Pl M big X T Sp i w s hso hc hmem
  obtain ⟨-, hl, hS, hQ⟩ := hso

  have hp : ∀ (w' : PlE D.host), NG.OverPl w' s.v → ∀ p : ℕ, w' ∈ placesOver D.host.E p →
      w ∈ placesOver D.host.E p := by
    intro w' hover p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hg : s.v ∉ gPl D := by
    rintro ⟨w', hover, k, hk⟩
    apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    have hw := hp w' hover _ hk
    fin_cases k
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  rcases hmem with hm | hm
  · exact hg hm
  obtain ⟨w', hover, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i)
    ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ hm
  rcases hw' with hCQ | hpd
  · apply hQ
    rw [← Sp.Qc_eq (X.nd.j i) (X.nd.w i)] at hCQ
    have hsw : s.w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) :=
      Sp.B.Qc_over (X.nd.j i) (X.nd.w i) w' s.w hCQ ⟨s.v, hover, s.w_under⟩
    rw [Sp.Q_eq _ _ i hi]
    exact Sp.B.Qc_conj (X.nd.j i) (X.nd.w i) w s.w hsw hc
  · apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    rw [X.nd.w_l i] at hpd
    exact Or.inr (Or.inr (hp w' hover _ hpd))

end GlobalTheory.SplitOutPlace
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L), ∃ σ, IsLocS π.S s σ ∧ ∀ (π' : NG.AutRep L n) (s' : SplitPlace L) (h : s'.w = s.w) σ', π.Iso π' → IsLocS π'.S s' σ' → HEq σ'.cl σ.cl := by
  first | exact @GlobalTheory.LocCompSplit.main | exact GlobalTheory.LocCompSplit.main | (intros; apply GlobalTheory.LocCompSplit.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  first | exact @GlobalTheory.TopSpan.topSpan | exact GlobalTheory.TopSpan.topSpan | (intros; apply GlobalTheory.TopSpan.topSpan <;> assumption)
end
