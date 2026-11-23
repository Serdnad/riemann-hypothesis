module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftCocycleMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle299
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageMono
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle435
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobSerre
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle436
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle198
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
import Mathlib.Topology.Sheaves.Presheaf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrysPhi

theorem pull_frob {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {σ : b.R →+* b.R} {τ : Λ →+* Λ}
    (mo : GlobalTheory.LogCris.Mor (F.cr b ht κ) (F.cr b ht κ) σ) (h : ∀ a, σ (c a) = c (τ a))
    {C' : Type 1} [Category.{0} C'] {F' : C' ⥤ ModuleCat.{0} Λ}
    (Bm : CH.Mor (OM (F.cr b ht κ) c) F' (RingHom.id Λ)) (Ph : CH.Mor F' F' τ)
    (η : ∀ T, Bm.G.obj (Ph.G.obj T) ⟶ mo.obj (Bm.G.obj T))
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (Bm.G.obj (Ph.G.obj T)).B),
      (η T').φ ((Bm.G.map (Ph.G.map f)).φ x) = (Bm.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (Bm.G.obj (Ph.G.obj T)).B), Bm.τ T ((η T).φ x) = Ph.τ T (Bm.τ (Ph.G.obj T) x))
    (j : ℕ) (x : CH.H (OM (F.cr b ht κ) c) j) :
    Bm.pull j ((omMor mo τ h).pull j x) = Ph.pull j (Bm.pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact (cr_pull_eq (Bm.comp Ph) ((omMor mo τ h).comp Bm) η nat hτ j x).symm

theorem qmap_frb {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) :
    Ideal.quotientMap J ph hq = frb hl :=
  Ideal.Quotient.ringHom_ext (RingHom.ext hm)

theorem pt_frb {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) (z : F.Pt.obj (CommRingCat.of (A ⧸ J))) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap J ph hq)) z = F.Pt.map (CommRingCat.ofHom (frb hl)) z := by
  rw [qmap_frb J ph hl hq hm]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def etaPhi (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ true n).obj T ⟶ (SH.phiM F κ n).obj ((gT F κ true n).obj T) :=
  crHom (T := (gT F κ true n).obj T) (T' := (SH.phiM F κ n).obj ((gT F κ true n).obj T)) (((elπ (F.pt κ)).obj T).phi n)
    (fun r => (mapAcr_phi ((elπ (F.pt κ)).obj T).fromBase n r).symm) (((elπ (F.pt κ)).obj T).dpP_phi n) fun h => by
      exact pt_frb F (((elπ (F.pt κ)).obj T).PFil n) (((elπ (F.pt κ)).obj T).phi n)
        (l_zero ((gT F κ true n).obj T).y.1.1) h (phi_mk _ n) _

theorem phi_beta (n j : ℕ) (x : Hc F κ true n j) :
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  pull_frob (SH.phiM F κ n) ((base l).phi_cris n) (βMor F κ true n) (phiMor (F.pt κ) n) (etaPhi F κ n)
    (fun f x => (mapAcr_phi ((elπ (F.pt κ)).map f) n x).symm) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.CrysPhi
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaGal

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dd_twAcr (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) :
    IsDPMorphism (DD k (tw σ A) n) (DD k A n) (twAcr σ A n) := by
  cases k
  exacts [dp_twAcr A σ n, dpP_twAcr A σ n]

theorem twAcr_fromBase (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (r : (base l).Acr n) :
    twAcr σ A n (mapAcr (tw σ A).fromBase n r) = mapAcr A.fromBase n (galBase σ n r) := by
  have e : (tw σ A).fromBase = baseTw σ ≫ twMap σ A.fromBase := (fromBase_comp _ (twMap σ A.fromBase)).symm
  rw [e, mapAcr_comp, twAcr_mapAcr]
  rfl

theorem uJ_tw (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (h) (x : (tw σ A).U) :
    Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n x) = uJ k A n (twU σ A x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n ((tw σ A).th w)) = uJ k A n (twU σ A ((tw σ A).th w))
  rw [uJ_th, twU_th, uJ_th, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) ((pdOk_twId σ A).acr_toAcr n w)

theorem map3 (P : CommRingCat.{0} ⥤ Type) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (e : A →+* D) (he : ∀ x, h (g (f x)) = e x) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom h) (P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y)) = P.map (CommRingCat.ofHom e) y := by
  have e' : CommRingCat.ofHom f ≫ CommRingCat.ofHom g ≫ CommRingCat.ofHom h = CommRingCat.ofHom e :=
    CommRingCat.hom_ext (RingHom.ext he)
  rw [← e', Functor.map_comp_apply, Functor.map_comp_apply]

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K))
  (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ)

def etaGal (T : El (F.pt κ)) :
    (gT F κ k n).obj ((elTw σ (ptTw F κ σ hσ)).obj T) ⟶ (SH.galM F κ σ hσ k n).obj ((gT F κ k n).obj T) :=
  crHom (twAcr σ T.1.obj n) (twAcr_fromBase σ T.1.obj n) (dd_twAcr k σ T.1.obj n) fun h =>
    map3 F.Pt (twUEquiv σ T.1.obj).symm.toRingHom (uJ k (tw σ T.1.obj) n) (Ideal.quotientMap _ (twAcr σ T.1.obj n) h)
      (uJ k T.1.obj n) (fun x => (uJ_tw k σ T.1.obj n h _).trans
        (congrArg (uJ k T.1.obj n) ((twUEquiv σ T.1.obj).apply_symm_apply x))) T.2.1

theorem β_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) := by
  intro l _ O _ F κ K σ hσ k n j x
  have h1 := pull_pull (ACris.galCris σ) (galMorC F κ σ hσ k n) (βMor F κ k n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMor F κ k n) (galMor σ (ptTw F κ σ hσ) n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (cr_pull_eq ((βMor F κ k n).comp (σ'' := ACris.galCris σ) (galMor σ (ptTw F κ σ hσ) n))
    ((galMorC F κ σ hσ k n).comp (σ'' := ACris.galCris σ) (βMor F κ k n)) (etaGal F κ σ hσ k n)
    (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.BetaGal
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem fin_vb [IsNoetherianRing R] {Z : Scheme.{0}} (z : Z ⟶ Spec (CommRingCat.of R)) [IsProper z] (F : C ⥤ ModuleCat.{0} R)
    {ι : Type} [Fintype ι] (U : ι → Z.Opens) (P : ι → ObjectProperty C) (m : ℕ) (hU : (⨆ α, U α) = ⊤)
    (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (V : VB (fun W : Z.Opens => strV z W) U (CrystallineSemistableComparison.Pb.cechH F P m)) (a : ℕ) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P m).cx.H a) :=
  vb_fin z U hU ha (CrystallineSemistableComparison.Pb.cechH F P m) V a

theorem fin_zero (F : C ⥤ ModuleCat.{0} R) {ι : Type} (P : ι → ObjectProperty C) (b a : ℕ)
    (h : ∀ i : Fin (a + 1) → ι, Subsingleton (HU F (capT P i) b)) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) := by
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).X a) := ⟨fun x y => funext fun i => (h i).elim _ _⟩
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) :=
    ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))⟩
  infer_instance

end Abs

section Main
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

theorem serre_red [IsNoetherianRing R] (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} R) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (j : ℕ)
    (h : ∀ a b, a + b = j → Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F (fun α => St Q {U α}) b).cx.H a)) :
    Module.Finite R (HU F (St Q (Set.range U)) j) := by
  obtain ⟨𝒮, h𝒮⟩ := serre_fg R
  exact (h𝒮 _).1 (GlobalTheory.CompanionTheory.GlobSt.glob_st.2.1 F Q U 𝒮 j fun a b hab => (h𝒮 _).2 (h a b hab))


include hI in
theorem fin_gen [IsNoetherianRing R] (hp : p ≠ 0) (hn : IsNilpotent (p : R)) [IsProper q] (U : Cov q) (r j : ℕ) :
    Module.Finite R (HU (GF (nlFun γ p X q κ) r) (St ⊤ (Set.range U.U)) j) := by
  refine serre_red (GF (nlFun γ p X q κ) r) ⊤ U.U j fun a b _ => ?_
  by_cases hb : b = r
  · subst hb
    have : IsProper (qF hI q κ) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    obtain ⟨V⟩ := vb_cech (γ := γ) (p := p) (κ := κ) hI hp hn U b
    have ha : ∀ n (i : Fin (n + 1) → U.ι), IsAffineOpen (capO (fun α => jF hI q κ ⁻¹ᵁ U.U α) i) := fun n i => by
      rw [capO_pre]
      exact aff_pre hI (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i)
    have e : (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) = fun α => SQ q κ γ p (U.U α) := rfl
    rw [e]
    exact fin_vb (qF hI q κ) _ _ _ b (cover_pre hI U) ha V a
  · refine fin_zero _ _ b a fun i => ?_
    have e := GlobalTheory.CompanionTheory.GrCech.capT_eq (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) U.U i
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c (i 0)) (capO_le U.U i 0) (GlobalTheory.CompanionTheory.GrCech.capO_affine U a i)
    have h := off_at (γ := γ) (p := p) (κ := κ) hI hp hn c' r b hb
    rw [show capT (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) i = SQ q κ γ p (capO U.U i) from e]
    exact h

end Main

theorem level_one_gr_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  intro l _ k _ _ _ O _ X q _ ρ U r j
  have hI : Wc.Im l k 1 = ⊥ := (Ideal.map_eq_bot_iff_le_ker _).2 (by
    rw [Ideal.mk_ker, pow_one])
  have hl : ((l : ℕ) : Wc.Wm l k 1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ 1}))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [hl]
    exact IsNilpotent.zero
  haveI := GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one (l := l) (k := k)
  have h := fin_gen (γ := Wc.pd l k 1) (p := l) (κ := (Wc.res l k 1).comp ρ) hI (Fact.out : l.Prime).ne_zero hn U r j
  exact h

end GlobalTheory.CompanionTheory.FibGr
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

theorem _root_.GlobalTheory.T.pull_eq_of_nat_trans : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j := by
  first | exact @GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | exact GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | (intros; apply GlobalTheory.CompanionTheory.CatPrism.pull_eq_target <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CapVan

theorem capO_eq_iInf_image {X : Scheme.{0}} {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → X.Opens) {m : ℕ}
    (i : Fin m → ι) : capO V i = ⨅ α ∈ Finset.image i Finset.univ, V α := by
  show (⨅ a, V (i a)) = _
  apply le_antisymm
  · refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le _ a
  · exact le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))

theorem van {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι) (r : ℕ) (hr : r ≠ a) :
    Subsingleton (HU (Fk q U a) (capT (Vk q U a) i) r) := by
  classical
  obtain ⟨e⟩ := GlobalTheory.T.cover_intersection_graded_iso q U a n i r
  have hV : IsAffineOpen (capO U.U i) := by
    rw [capO_eq_iInf_image]
    exact U.inter _ ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  haveI := CrystallineSemistableComparison.Pb.gr_aff q (capO U.U i) hV (a + 1) a r (Nat.lt_succ_self a) hr
  exact e.injective.subsingleton

end GlobalTheory.CompanionTheory.CapVan
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.FirstChernRationalLift

variable {K B' : Type} [Field K] [CharZero K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ)

abbrev famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) : C ⥤ Thick (smFun X q) :=
  G ⋙ (smO γ q 1 s {⊤}).G ⋙ (TO q 1 s {⊤}).ι

theorem pt_famK {C : Type 1} [Category.{0} C] (G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory) (c : C) :
    pt ((famK γ q s G).obj c) = pt (G.obj c).obj := Category.comp_id _

def liftK {C : Type 1} [Category.{0} C] {G : C ⥤ (TS γ q 1 s {⊤}).FullSubcategory} {D : E.LineData X}
    (Λ : B.CLift (q := q) (b := nlBase B' I γ 0) (ht := rfl) (κ := κA K I) (G ⋙ (TS γ q 1 s {⊤}).ι) D) :
    CLiftK (famK γ q s G) D where
  p c := Λ.p c
  hp c := (Λ.hp c).trans (Category.comp_id _).symm
  w φ := Λ.w φ
  hw φ h := Λ.hw φ h

theorem isFirstChernThickening_muB_of_isFirstChernDeRham (D : E.LineData X) (c : HdR q 2)
    (h : IsFirstChernDeRham (q := q) D c) :
    IsFirstChernThickening (TS γ q 1 s {⊤}) D s (muB γ q 1 s {⊤} 2 c) := by
  intro C _ G hG Λ
  have hpd : ∀ c', ((famK γ q s G).obj c').pdPow s = ⊥ := fun c' => ((smO γ q 1 s {⊤}).G.obj (G.obj c')).property.1.1
  have hV : ∀ c', ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((famK γ q s G).obj c') := by
    intro c'
    obtain ⟨V, ⟨σ, hσ⟩, hU⟩ := hG c'
    refine ⟨V, σ, hσ, ?_⟩
    unfold InU
    rw [pt_famK]
    exact hU
  obtain ⟨z, hz, hzv, hcls⟩ := h s C (famK γ q s G) hpd hV (liftK γ q s Λ)
  let m' : CH.Mor (famK γ q s G ⋙ O (smFun X q)) (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) (algebraMap K B') :=
    ⟨𝟭 _, fun T => (smO γ q 1 s {⊤}).o.τ (G.obj T), fun φ x => (smO γ q 1 s {⊤}).o.nat (G.map φ) x⟩
  have e : (show CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 from Λ.coc (RingHom.id _) s) = m'.pullC 2 z := by
    funext σ
    exact (hzv σ).symm
  have hb : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (m'.pullC 2 z) = 0 := by
    rw [m'.d_pullC, hz, map_zero]
  have hz' : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 (Λ.coc (RingHom.id _) s) = 0 := (congrArg (CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) e).trans hb
  refine ⟨hz', ?_⟩
  have e1 := CrystallineSemistableComparison.P.mapH_cls m'.hom 2 z hz hb
  have e2 : (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2 (muB γ q 1 s {⊤} 2 c) =
      m'.pull 2 ((CH.Mor.restrict (O (smFun X q)) (famK γ q s G)).pull 2 c) := by
    have a1 := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι) (smO γ q 1 s {⊤}).o 2 c).1
    have a2 := (CrystallineSemistableComparison.P.pull_comp ((CH.Mor.restrict (O (smFun X q)) (TO q 1 s {⊤}).ι).comp (smO γ q 1 s {⊤}).o)
      (CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G) 2 c).1
    have b := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (O (smFun X q)) (famK γ q s G)) m' 2 c).1
    exact (congrArg ((CH.Mor.restrict (CH.modF (sP (TS γ q 1 s {⊤})).A) G).pull 2) a1.symm).trans (a2.symm.trans b)
  rw [e2, ← hcls]
  refine Eq.trans ?_ e1.symm
  have key : ∀ (a : CH.Cn (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2) (ha : CH.d (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A) 2 a = 0),
      a = m'.pullC 2 z → (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls a ha =
        (CH.cx (G ⋙ CH.modF (sP (TS γ q 1 s {⊤})).A)).cls (m'.pullC 2 z) hb := by
    rintro _ _ rfl
    rfl
  exact key _ hz' e

end GlobalTheory.CompanionTheory.FirstChernRationalLift
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.MuNat

theorem muB_nat : ∀ {K B₁ B₂ : Type} [CommRing K] [CommRing B₁] [CommRing B₂] [Algebra K B₁] [Algebra K B₂] {I₁ : Ideal B₁} {I₂ : Ideal B₂}
    {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂} {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of K)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of K)} {σ : B₁ →+* B₂} (nm : NMor γ₁ q₁ (κA K I₁) γ₂ q₂ (κA K I₂) σ) (hu : nm.u ≫ q₁ = q₂) (l s : ℕ),
    (∀ k, σ (algebraMap K B₁ k) = algebraMap K B₂ k) → ∀ (j : ℕ) (x : HdR q₁ j),
    nmHO nm l s j (muB γ₁ q₁ l s {⊤} j x) = muB γ₂ q₂ l s {⊤} j (pullR (n := j) nm.u hu x) := by
  intro K B₁ B₂ _ _ _ _ _ I₁ I₂ γ₁ γ₂ X₁ X₂ q₁ q₂ σ nm hu l s hσ j x
  letI t1 : RingHomCompTriple (algebraMap K B₁) σ (algebraMap K B₂) := ⟨RingHom.ext hσ⟩
  let r₁ := CH.Mor.restrict (O (smFun X₁ q₁)) (TO q₁ l s {⊤}).ι
  let r₂ := CH.Mor.restrict (O (smFun X₂ q₂)) (TO q₂ l s {⊤}).ι
  let a₁ := (smO γ₁ q₁ l s {⊤}).o
  let a₂ := (smO γ₂ q₂ l s {⊤}).o
  let n := (nmS nm l s).o
  let MS : CH.Mor (O (smFun X₁ q₁)) (O (smFun X₂ q₂)) (RingHom.id K) := CH.Mor.ofBlk
    { G := (smMor nm.u hu).functor
      τ := fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      nat := fun _ _ => rfl }
  let L1 : CH.Mor _ _ (algebraMap K B₁) := r₁.comp a₁
  let ML : CH.Mor _ _ (algebraMap K B₂) := L1.comp n
  let R1 : CH.Mor _ _ (RingHom.id K) := MS.comp r₂
  let MR : CH.Mor _ _ (algebraMap K B₂) := R1.comp a₂
  have hL1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₁) r₁ a₁ j x).1
  have hL2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) L1 n j x).1
  have hR1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) MS r₂ j x).1
  have hR2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) R1 a₂ j x).1
  let η : ML.G ⟶ MR.G :=
    { app := fun T => mkH (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (T := ML.G.obj T) (T' := MR.G.obj T) (RingHom.id T.obj.B)
        (fun r => congrArg T.obj.i (hσ r)) ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
          refine Subtype.ext (Prod.ext ?_ ?_)
          · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
            have hw1 := (ML.G.obj T).w r
            have hw2 := (MR.G.obj T).w r
            have h3 : Ideal.Quotient.mk T.obj.J ((ML.G.obj T).i r) = Ideal.Quotient.mk T.obj.J ((MR.G.obj T).i r) :=
              congrArg (Ideal.Quotient.mk T.obj.J) (congrArg T.obj.i (hσ r))
            exact (congrArg (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
          · have e : CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) =
                𝟙 (CommRingCat.of (T.obj.B ⧸ T.obj.J)) :=
              CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
            have e2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) =
                𝟙 (Spec (CommRingCat.of (T.obj.B ⧸ T.obj.J))) := (congrArg Spec.map e).trans (Spec.map_id _)
            change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) ≫
                ((T.obj.y.1.2 ≫ nm.u) ≫ 𝟙 X₁) = (T.obj.y.1.2 ≫ 𝟙 X₂) ≫ nm.u
            rw [e2, Category.id_comp, Category.comp_id, Category.comp_id])
      naturality := fun T T' f => hom_ext (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (RingHom.ext fun _ => rfl) }
  have h4 := CrystallineSemistableComparison.P.prism ML MR η (fun T y => rfl) j x
  exact (congrArg (n.pull j) hL1.symm).trans (hL2.symm.trans (h4.trans (hR2.trans (congrArg (a₂.pull j) hR1))))

end GlobalTheory.CompanionTheory.MuNat
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

theorem redM_cup {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j) :
    redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := by
  have hm : ∀ T (u v : (CH.modF (sP Q).A).obj ((𝟭 _).obj T)),
      (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T ((CH.mulP (sP Q).A).μ _ u v) =
        (sqP (stdI Q r c)).μ T ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T u)
          ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T v) := fun _ _ _ => rfl
  exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (sP Q).A) (sqP (stdI Q r c)) (𝟭 _)
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat hm h x y

end GlobalTheory.CompanionTheory.RedCup
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem red_kills_toSome : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r j : ℕ), ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSome (TS γ q l s 𝒱) r ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s 𝒱 c lam hc r j x hx
  exact GlobalTheory.CompanionTheory.RedFil.red_kills d q s 𝒱 c lam hc r j x hx

end GlobalTheory.CompanionTheory.RedFil
end
