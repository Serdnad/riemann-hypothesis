module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThInt

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thetaInt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M h hnorm hpt
  obtain ⟨e, hSym, hCrd⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn hno F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _) hnorm hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  have hmV : IsUnit (m : V) := by
    have h1 : IsUnit (m : o) := by rw [← map_natCast β]; exact hmu.map β
    rw [← map_natCast σ]; exact h1.map σ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    GlobalTheory.T.lineBundleSymmetry_hypothesis_base_change _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S) (k : T ⟶ Sp (ResidueField R)), IsLocallyNoetherian T → IsReduced T → t ≫ π = k ≫ spMap (residue R) → ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme), e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧ l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  first | exact @GlobalTheory.Mum.Emb.pullback_iso_of_closed | exact GlobalTheory.Mum.Emb.pullback_iso_of_closed | (intros; apply GlobalTheory.Mum.Emb.pullback_iso_of_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SgZero

theorem exists_nat_evalZ (φ : InvFun ℤ) (g : ℕ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ)
    (δ ga : Fin m → LinearMap.BilinForm ℤ X) (M d : ℕ) (hpf : IsPolFan id g φ) (hrk : Module.finrank ℤ X ≤ g)
    (hc : IsCone id φ ga) (hδ : ∀ k, δ k = (M : ℤ) • ga k) : ∃ b : Fin m → ℕ, ∀ k, (b k : ℝ) = d * φ.evalZ (δ k) := by
  have hP := hpf X hrk
  have key : ∀ k, ∃ n : ℕ, φ.evalZ (ga k) = n := by
    intro k
    obtain ⟨z, hz⟩ := hP.integral (ga k) (hc.mem k) (hc.nonneg k)
    by_cases h0 : ga k = 0
    · refine ⟨0, ?_⟩
      have := hc.evalZ_smul 0 k
      simp only [Nat.cast_zero, zero_smul, zero_mul] at this
      rw [h0]; simpa [h0] using this
    · have hp := hP.pos (ga k) (hc.mem k) (hc.nonneg k) h0
      refine ⟨z.toNat, ?_⟩
      rw [hz] at hp ⊢
      have : (0 : ℤ) ≤ z := by exact_mod_cast hp.le
      rw [show ((z.toNat : ℕ) : ℝ) = ((z.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg this]
  choose n hn using key
  refine ⟨fun k => d * (M * n k), fun k => ?_⟩
  rw [hδ, hc.evalZ_smul, hn]
  push_cast; ring

theorem dvd_of_map_dvd_of_finite (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    (ρ : A →+* B) (hρ : Function.Injective ρ) (hf : ρ.Finite) (a c : A) (ha : a ≠ 0) (h : ρ a ∣ ρ c) : a ∣ c := by

  letI : Algebra A B := ρ.toAlgebra
  haveI : Module.Finite A B := hf
  obtain ⟨x, hx⟩ := h
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) x
  let K := FractionRing A
  let L := FractionRing B
  let gL : A →+* L := (algebraMap B L).comp ρ
  have hgL : Function.Injective gL := (IsFractionRing.injective B L).comp hρ
  let iK : K →+* L := IsFractionRing.lift hgL
  have hιK : ∀ r : A, iK (algebraMap A K r) = gL r := IsFractionRing.lift_algebraMap hgL
  have hA : algebraMap A K a ≠ 0 := fun e => ha (IsFractionRing.injective A K (e.trans (map_zero _).symm))
  have hρa : algebraMap B L (ρ a) ≠ 0 := fun e => hA (by
    have := hgL (show gL a = gL 0 by simpa [gL] using e)
    rw [this, map_zero])
  set y : K := algebraMap A K c / algebraMap A K a with hy
  have hιKy : iK y = algebraMap B L x := by
    rw [hy, map_div₀, hιK, hιK]
    simp only [gL, RingHom.comp_apply, hx, map_mul]
    exact mul_div_cancel_left₀ _ hρa
  have hint : IsIntegral A y := by
    refine ⟨p, hpm, ?_⟩
    apply iK.injective
    rw [map_zero, Polynomial.hom_eval₂, hιKy]
    have e1 : iK.comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) := by
      ext r; exact hιK r
    rw [e1, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hint
  refine ⟨z, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hz, hy, mul_div_cancel₀ _ hA]

theorem idlAlong_eq_span_monomial : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, ∀ (φ : InvFun ℤ) (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i → IsPolFan id g φ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ (ga : Fin m → LinearMap.BilinForm ℤ Q.X) (M : ℕ), IsCone id φ ga → (∀ k, δ k = (M : ℤ) • ga k) → ∀ ξ : Sp V ⟶ S, UnifOver F j ξ Q → ∃ b : Fin m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ (δ k)) ∧ idlAlong (J.comap π) ξ = Ideal.span {∏ k, t k ^ b k} := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W φ d J S π j hJ hval hbl hji hpf V _ _ _ Q m t δ hrk ht hsym hnn hdef
    hmono ga M hcone hδ ξ hU
  obtain ⟨b, hb⟩ := exists_nat_evalZ φ g Q.X m δ ga M d hpf hrk hcone hδ
  refine ⟨b, hb, ?_⟩
  have hCN : IsCN V := hU.1
  obtain ⟨R', _, _, _, ρ, r, D, e, hCN', hρi, hρf, hρl, hr, hrefn, hmon⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data V Q m t δ hCN hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hdef
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.T.idealSheafAlongLocalSpec_normalisedBlowup_principal π J hbl V ξ
  rw [hg₀]
  have key : ∀ (Wr : Type) [CommRing Wr] [IsDomain Wr] [IsDiscreteValuationRing Wr], IsAdicComplete (maximalIdeal Wr) Wr →
      ∀ κ : R' →+* Wr, Function.Injective κ → IsLocalHom κ →
        Ideal.span {κ (ρ g₀)} = Ideal.span {κ (ρ (∏ k, t k ^ b k))} := by
    intro Wr _ _ _ hc κ hκi hκl
    obtain ⟨T, σ, c, e', hσ, hy, hc', hβ⟩ := GlobalTheory.T.exists_trait_period_form_valuation_sum_refined_chart F S j V Q ξ hU m t δ R' ρ r D e hCN' hρi hρf hρl hr
      (fun k => (ht k).2) hsym hrefn hmon Wr hc κ hκi hκl
    have hy' : jK T.V ≫ spMap σ ≫ (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = T.y ≫ i := by
      rw [← hji]
      simpa only [Category.assoc] using congrArg (· ≫ π) hy
    have h1 := GlobalTheory.T.idealSheafAlongLocalSpec_monomial_of_cone_combination F Z i φ J d hval Q.X m ga δ M hcone hδ b hb T Wr σ c e' (spMap κ ≫ spMap ρ ≫ ξ ≫ π)
      (fun k => κ (ρ (t k))) hσ hy' hc' hβ
    have h2 : idlAlong J (spMap κ ≫ spMap ρ ≫ ξ ≫ π) = Ideal.span {κ (ρ g₀)} := by
      rw [GlobalTheory.TraitOrder.idlAlong_comp, GlobalTheory.TraitOrder.idlAlong_comp, ← GlobalTheory.PullAlong.idlAlong_comap_eq, hg₀,
        Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rw [← h2, h1, map_prod, map_prod]
    simp only [map_pow]
  obtain ⟨hN', hI', -, hZ'⟩ := hCN'
  obtain ⟨-, hIV, -, -⟩ := hCN
  set f := ∏ k, t k ^ b k with hfdef
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k).2
  have hρf0 : ρ f ≠ 0 := fun h => hf0 (hρi (h.trans (map_zero ρ).symm))
  have hκ0 : ∀ (Wr : Type) [CommRing Wr] (κ : R' →+* Wr), Function.Injective κ → κ (ρ f) ≠ 0 :=
    fun Wr _ κ hκ h => hρf0 (hκ (h.trans (map_zero κ).symm))
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨Wr, _, _, _, κ, ⟨hdvr, hc, -⟩, hκi, hcm⟩ := GlobalTheory.PrimeUnif.exists_cdvr R' (maximalIdeal R')
    have hκl : IsLocalHom κ := ⟨fun a ha => by
      by_contra hna
      have : a ∈ (maximalIdeal Wr).comap κ := by rw [hcm]; exact hna
      exact (mem_maximalIdeal _).1 this ha⟩
    have := key Wr hc κ hκi hκl
    rw [map_zero, map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hκ0 Wr κ hκi this
  have hρg0 : ρ g₀ ≠ 0 := fun h => hg0 (hρi (h.trans (map_zero ρ).symm))
  have d1 : ρ f ∣ ρ g₀ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ g₀) (ρ f) hρf0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).symm.dvd
  have d2 : ρ g₀ ∣ ρ f := GlobalTheory.Poinc.dvd_of_forall_complete_dvr R' (ρ f) (ρ g₀) hρg0
    fun Wr _ _ _ hc κ hκi hκl => (Ideal.span_singleton_eq_span_singleton.1 (key Wr hc κ hκi hκl)).dvd
  exact Ideal.span_singleton_eq_span_singleton.2
    (associated_of_dvd_dvd (dvd_of_map_dvd_of_finite V R' ρ hρi hρf g₀ f hg0 d2) (dvd_of_map_dvd_of_finite V R' ρ hρi hρf f g₀ hf0 d1))

end GlobalTheory.SgZero
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_rigidified_symmetric_cubicalBundle_extension : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ (PP : RigLB G) (cub : CubicalStr G PP), PP.IsSymmetric ∧ ∃ cm : CubeMap tF.G G, cm.F = e ∧ cm.e = j ∧ cm.IsPullCubical tF.cub cub := by
  first | exact @GlobalTheory.BundleExt.exists_rigLB_cubical_symm | exact GlobalTheory.BundleExt.exists_rigLB_cubical_symm | (intros; apply GlobalTheory.BundleExt.exists_rigLB_cubical_symm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  first | exact @GlobalTheory.Poinc.Sep.Coef.coef_monomial | exact GlobalTheory.Poinc.Sep.Coef.coef_monomial | (intros; apply GlobalTheory.Poinc.Sep.Coef.coef_monomial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.GLiftRechart.main | exact GlobalTheory.Poinc.GLiftRechart.main | (intros; apply GlobalTheory.Poinc.GLiftRechart.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.rechart_at_classical_trait | exact GlobalTheory.Poinc.rechart_at_classical_trait | (intros; apply GlobalTheory.Poinc.rechart_at_classical_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_tensorDegenerationData_of_unimodular_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ D' : DegData R (maximalIdeal R), Nonempty (Tens D.toPre D'.toPre W) := by
  first | exact @GlobalTheory.Mum.TensExist.exists_tens | exact GlobalTheory.Mum.TensExist.exists_tens | (intros; apply GlobalTheory.Mum.TensExist.exists_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mulPull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1), ∃ (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)) (S : SecK C.P.L.L C.α (m ^ 2)), ((∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → T.Exp a b θ₀ F₁ → ∃ v : Wˣ, T.Exp a (b * v) S G := by
  intro R _ _ _ hR D C m hm F₁ θ₀
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd R hR D m hm F₁
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_multiplicationPullback_genericSection_cover R hR D C m hm θ₀
  exact ⟨G, S, GlobalTheory.T.multiplicationPullback_family_ne_zero_odd R hR D m hm F₁ G hG,
    fun W _ _ _ T a b ha h => GlobalTheory.T.expansion_oddMultiplicationPullback_at_trait R hR D C m hm F₁ G θ₀ S hG hS W T a b ha h⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_thetaNormalisationConstant_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∀ s : SecK C.P.L.L C.α k, ∃ c₁ c₂ : R, c₂ ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → b ≠ 0 → T.Exp a b s F₀ → ∃ u : Wˣ, T.φ c₂ * (u : W) * a = T.φ c₁ * b := by
  first | exact @GlobalTheory.Mum.exists_norm_const | exact GlobalTheory.Mum.exists_norm_const | (intros; apply GlobalTheory.Mum.exists_norm_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  first | exact @GlobalTheory.TInj.taut_refine | exact GlobalTheory.TInj.taut_refine | (intros; apply GlobalTheory.TInj.taut_refine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_eqv_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ lab lab) → ∃ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N) (E₀ : _), Eqv D.toPre A (Kb R) N lab E₀ ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀) := by
  intro R _ _ _ hB D A N hN lab E hE hlab
  have hc0 : CharZero R := hB.2
  choose E' hE' hT using fun σ => GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist R hB D A N hN lab E hE hlab σ
  choose c hc using fun σ => GlobalTheory.T.equivariant_bijections_families_sections_differ_by_scalar R (maximalIdeal R) D A (Kb R) N hN lab E (E' σ) hE (hE' σ)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_common_scaling_descends_to_fractionField R hB A N {q : IntFam (maximalIdeal R) D.toPre N × Fam D.toPre (Kb R) N // q.1.Over q.2}
    (fun i => E i.1.2) c (fun σ i => ⟨E' σ i.1.2, hT σ i.1.1 i.1.2 i.2, hc σ i.1.2⟩)
  obtain ⟨E₀, hE₀, hE₀f⟩ := GlobalTheory.T.thetaFamilySectionEquivariance_smul_of_ne_zero R D.toPre A (Kb R) N lab E hE c₀
  choose Φ hΦ using hc₀
  have hex := fun F₀ => GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
  refine ⟨fun F₀ => Φ ⟨(F₀, (hex F₀).exists.choose), (hex F₀).exists.choose_spec⟩, E₀, hE₀, fun F₀ s hs => ?_⟩
  obtain rfl : (hex F₀).exists.choose = s := (hex F₀).unique (hex F₀).exists.choose_spec hs
  exact hΦ _ (E₀ _) (hE₀f _)

end GlobalTheory.Mum
end
