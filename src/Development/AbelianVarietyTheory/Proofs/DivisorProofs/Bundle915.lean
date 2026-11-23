module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle086
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle852
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle887
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
import Mathlib.RingTheory.Etale.Weakly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.LieHodgeTate

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  obtain ⟨D, e, fil, lie, hal, -⟩ := hG
  have hprim : IsPrimitiveRoot (root ε).untilt p := by
    have := hε 1
    simpa [zeta] using this
  obtain ⟨-, hle, -, hfil, -, -⟩ := HodgeTateBound.bound p C v O hv ε hprim ℤ_[p] G.height D
  obtain ⟨-, -, -, hsurj, hν, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hprim
  have hsingle : ∀ i, toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
    intro i
    funext j
    simp only [toO, LinearEquiv.apply_symm_apply]
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · let φ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ (LinearMap.codRestrict D.Fil D.al fun u => hle ⟨u, rfl⟩)
    have hφ : φ = 0 := by
      apply (Pi.basisFun O (Fin G.height)).ext
      intro i
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← hsingle i]
      have h1 : (⟨D.al (toO e (e.symm (Pi.single i 1))), hle ⟨_, rfl⟩⟩ : D.Fil) =
          fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
      change x (fil.symm ⟨D.al _, _⟩) = 0
      rw [h1, LinearEquiv.symm_apply_apply]
      exact hx _
    ext w
    obtain ⟨u, hu⟩ := hfil _ (fil w).2
    have h1 : WittVector.fontaineTheta O p (nu ε) • fil w = ⟨D.al u, hle ⟨u, rfl⟩⟩ :=
      Subtype.ext hu.symm
    have h2 : WittVector.fontaineTheta O p (nu ε) * x w = 0 := by
      rw [← smul_eq_mul, ← map_smul, ← fil.symm_apply_apply (WittVector.fontaineTheta O p (nu ε) • w),
        map_smul fil, h1]
      exact LinearMap.congr_fun hφ u
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hν
    · simpa using h
  · haveI : ValuationRing O := ValuationRing.of_integers v hv
    haveI : Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb) := by
      haveI : Module.Free O (LinearMap.range D.bb) :=
        GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing O _
      exact Module.Free.of_equiv (D.bb.quotKerEquivRange).symm
    haveI : Module.Free O ((Fin G.height → O) ⧸ D.Fil) := by
      change Module.Free O ((Fin G.height → O) ⧸ LinearMap.ker D.bb); infer_instance
    obtain ⟨N', hN'⟩ := GlobalTheory.exists_isCompl_of_projective_quotient D.Fil
    let ρ : (Fin G.height → O) →ₗ[O] O :=
      x ∘ₗ fil.symm.toLinearMap ∘ₗ D.Fil.projectionOnto N' hN'
    choose r hr using fun i => hsurj (ρ (Pi.single i 1))
    obtain ⟨L, hL⟩ := GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum p C v O hv ε hε G G.height D e fil hal
    refine ⟨L r, fun t => ?_⟩
    rw [hL]
    have hρ : ∀ w, ρ w = ∑ i, WittVector.fontaineTheta O p (r i) * w i := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ ρ w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr, smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hθ : WittVector.fontaineTheta O p (r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i))) =
        ρ (D.al (toO e t)) := by

      rw [hρ, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, RingHom.map_mulVec]
      rfl
    rw [hθ]
    have h3 : D.Fil.projectionOnto N' hN' (D.al (toO e t)) = fil (hodgeTate G t) := by
      rw [show D.al (toO e t) = ((fil (hodgeTate G t) : D.Fil) : Fin _ → O) from hal t,
        Submodule.projectionOnto_apply_left]
    change x (fil.symm (D.Fil.projectionOnto N' hN' (D.al (toO e t)))) = _
    rw [h3, LinearEquiv.symm_apply_apply]

end GlobalTheory.LieHodgeTate
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.ConstMu

theorem frobenius_ofPadic {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem frobenius_phiInv' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (a : Ainf p O) :
    WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem frobenius_mu' {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  conv_lhs => rw [← xi_mul_nu, map_mul, ← phiInv_mu, frobenius_phiInv']

theorem existsUnique_lattMap : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε g hg
  obtain ⟨ec, hec⟩ := GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv p C v O hv ε hε
  obtain ⟨em, hem⟩ := GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one p C v O hv ε hε
  have eig := GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf p C v O hv ε hε
  set l : latt (PDivGroup.mu p O) := em.symm 1 with hl_def
  have hl : l.1 (epsTate hε) = Sandwich.mu ε := by
    rw [← hem l, hl_def, LinearEquiv.apply_symm_apply, mul_one]
  have htate : ∀ t : (PDivGroup.mu p O).Tate, ∃ a : ℤ_[p], t = a • epsTate hε := by
    intro t
    obtain ⟨a, rfl⟩ := (epsEquiv hε).surjective t
    exact ⟨a, rfl⟩
  have hlval : ∀ a : ℤ_[p], l.1 (a • epsTate hε) = ofPadic p O a * Sandwich.mu ε := by
    intro a
    rw [map_smulₛₗ, hl, smul_eq_mul]
  have hgen : ∀ y : latt (PDivGroup.mu p O), y = em y • l := by
    intro y
    apply em.injective
    rw [map_smul, hl_def, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hpull : ∀ (f : const p O ⟶ PDivGroup.mu p O) (y : latt (PDivGroup.mu p O)),
      ec (lattMap f y) = y.1 (tateMap _ _ O f (constGen p O)) := by
    intro f y
    rw [hec]
    rfl

  set b : Ainf p O := ((g l).1 (constGen p O)) with hb_def
  have hbeig : WittVector.frobenius b = WittVector.frobenius (xi ε) * b := by
    have h1 := hg l (WittVector.frobenius (xi ε) • l) (by
      intro t
      obtain ⟨a, rfl⟩ := htate t
      rw [Submodule.coe_smul, LinearMap.smul_apply, hlval, smul_eq_mul, map_mul,
        frobenius_ofPadic, frobenius_mu']
      ring) (constGen p O)
    rw [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [hb_def, ← h1]
  obtain ⟨c, hc, hcu⟩ := eig b hbeig
  have hfix : ∀ f : const p O ⟶ PDivGroup.mu p O, lattMap f = g ↔
      ec (lattMap f l) = ec (g l) := by
    intro f
    constructor
    · intro h; rw [h]
    · intro h
      apply LinearMap.ext
      intro y
      rw [hgen y, map_smul, map_smul, ec.injective h]
  refine ⟨constHom (PDivGroup.mu p O) (c • epsTate hε), ?_, ?_⟩
  · show lattMap _ = g
    rw [hfix, hpull, tateMap_constHom, hlval, hec, hc]
  · intro f hf
    rw [hfix, hpull, hec] at hf
    obtain ⟨a, ha⟩ := htate (tateMap _ _ O f (constGen p O))
    rw [ha, hlval] at hf
    have hac : a = c := hcu a hf
    rw [← (constHom (PDivGroup.mu p O)).apply_symm_apply f, constHom_symm_apply, ha, hac]

end GlobalTheory.PDivLat.ConstMu
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.GeomDesc

theorem diag_comp {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left := by
  apply pullback.hom_ext
  · have h1 := sq.1
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := sq.2
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P₀ : LB (G2 A₀).left}
    (hP : P.IsLB) (hP₀ : P₀.IsLB) (pol : LBIso P (P₀.pull φ₂)) :
    LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) := by
  have h₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp pol _ (diag_comp sq).symm
  have h₂ : LBIso ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) φ rfl
  exact LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.GeomDesc


open GlobalTheory.UPel.HT.GeomDesc in
theorem GlobalTheory.UPel.HT.geom_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ N φ₂ P P₀ eta eta₀ hG hA hA₀ gp hact sq hP hP₀ pol heta hgeom k _ _ x β hx
  have := hG.etale
  have := hG.onto
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  obtain ⟨I, hI⟩ := hgeom k y β (by rw [← Category.assoc, hx])
  have iso := diag_lbIso sq hP hP₀ pol
  refine ⟨GlobalTheory.UPel.HT.TateIsoO.transport (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g ≫ act.act c).left ≫ φ = (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y) g ≫ act₀.act c).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X A₀ A π φ _ _ (pull_isLB hP₀ _) (pull_isLB hP _) gp iso
      (Over.mk y) n g g' _ _ _ (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g)
      (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g')).1 hc
  · rw [GlobalTheory.UPel.HT.TateIsoO.transport_ev, ← hI a]
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left]
    show (toUnit (Over.mk (y ≫ π)) ≫ eta₀ a).left = (toUnit (Over.mk y) ≫ eta a).left ≫ φ
    rw [Over.comp_left, Over.comp_left, Category.assoc, heta a, ← Category.assoc]
    congr 1

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.DiagComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

theorem diag_comp (m : ObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply pullback.hom_ext
  · have h1 := m.sq.1
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (fst o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := m.sq.2
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (snd o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso (m : ObjMap o' o f) :
    LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  have h₁ : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp m.pol _ (diag_comp m).symm
  have h₂ : LBIso ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ)
      (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _)) m.φ rfl
  exact LBIso.trans (pull_isLB o'.isLB _) (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.DiagComp

namespace GlobalTheory.UPel.HT

theorem objMap_comp_diag_lbIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun m => DiagComp.diag_lbIso m⟩

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  first | exact @GlobalTheory.UPel.HT.tateIsoO_pullback | exact GlobalTheory.UPel.HT.tateIsoO_pullback | (intros; apply GlobalTheory.UPel.HT.tateIsoO_pullback <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.lTensor_liftBaseChange_globalOneForms_affinePreimage_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  first | exact @GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | exact GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective | (intros; apply GlobalTheory.AbCoh.lTensor_liftSemi_pullForm_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kunneth_cup_tensor_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom), ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 → ∑ i, x i ⊗ₜ[K] y i = 0 := by
  first | exact @GlobalTheory.Kunneth.cup_tmul_injective | exact GlobalTheory.Kunneth.cup_tmul_injective | (intros; apply GlobalTheory.Kunneth.cup_tmul_injective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact GlobalTheory.T.obstructionClass_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := GlobalTheory.T.liftingObstructionBockstein_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem IsCuspDatum.exists_blockDiag_act_eq (F : Type) [Field F] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (hσ : IsCuspDatum b σ)
    (p : blockTri (κ := F) b) :
    ∃ m : blockTri (κ := F) b, σ m = σ p ∧ ∀ i k : Fin r, ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := by
  refine ⟨Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p), ?_,
    fun i k => GlobalTheory.Parabolic.leviProj_apply b p i k⟩
  set m := Subgroup.inclusion (GlobalTheory.Parabolic.levi_le_blockTri b) (GlobalTheory.Parabolic.leviProj b p) with hm
  have h1 : GlobalTheory.Parabolic.leviProj b (m⁻¹ * p) = 1 := by
    rw [map_mul, map_inv, hm, GlobalTheory.Parabolic.leviProj_inclusion, inv_mul_cancel]
  have h2 : σ (m⁻¹ * p) = 1 := by
    refine hσ.infl _ fun i j hij => ?_
    have e := GlobalTheory.Parabolic.leviProj_apply b (m⁻¹ * p) i j
    rw [h1, if_pos hij] at e
    rw [← e]
    simp
  calc σ m = σ m * σ (m⁻¹ * p) := by rw [h2, mul_one]
    _ = σ p := by rw [← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinGL
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  first | exact @GlobalTheory.Dieu.existsUnique_hasLogDeg | exact GlobalTheory.Dieu.existsUnique_hasLogDeg | (intros; apply GlobalTheory.Dieu.existsUnique_hasLogDeg <;> assumption)
end

section

open GlobalTheory.LatVal GlobalTheory.LatJet

theorem _root_.GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  first | exact @GlobalTheory.HilbertEis.eisExp | exact GlobalTheory.HilbertEis.eisExp | (intros; apply GlobalTheory.HilbertEis.eisExp <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  first | exact @GlobalTheory.HCF.rt_translate_kill | exact GlobalTheory.HCF.rt_translate_kill | (intros; apply GlobalTheory.HCF.rt_translate_kill <;> assumption)
end
